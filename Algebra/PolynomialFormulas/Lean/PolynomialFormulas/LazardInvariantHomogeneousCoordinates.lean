import PolynomialFormulas.LazardInvariantArtinModuleBasis
import PolynomialFormulas.LazardInvariantModule
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous coordinates in the Artin basis

This file supplies the grading lemma used in Lazard's Reynolds argument.  If
`b i` is a homogeneous basis vector of degree `δ i`, then the `i`th
coefficient of a homogeneous vector of degree `d` is homogeneous of degree
`d - δ i`; in particular it vanishes when `d < δ i`.

The coefficient ring is the symmetric subalgebra.  Its homogeneous-component
operator is defined by taking the ordinary homogeneous component of the
underlying polynomial and proving that it is still symmetric.  Consequently,
a degree-preserving endomorphism has a degree-triangular matrix in every
homogeneous Artin basis, and every equal-degree matrix entry is a scalar from
the ground field.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantHomogeneousCoordinates

open MvPolynomial
open scoped BigOperators

set_option autoImplicit false

noncomputable section

open LazardInvariantModule

variable {k σ ι : Type*} [CommRing k]

/-- Homogeneous components preserve the symmetric subalgebra. -/
def symmetricHomogeneousComponent (d : ℕ) :
    SymmetricRing k σ →ₗ[k] SymmetricRing k σ where
  toFun p := ⟨homogeneousComponent d p.1, by
    intro e
    rw [rename_homogeneousComponent, p.2 e]⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (homogeneousComponent d) p.1 q.1
  map_smul' r p := by
    apply Subtype.ext
    change homogeneousComponent d (r • p.1) =
      r • homogeneousComponent d p.1
    exact (homogeneousComponent d).map_smul r p.1

@[simp]
theorem symmetricHomogeneousComponent_coe (d : ℕ)
    (p : SymmetricRing k σ) :
    (symmetricHomogeneousComponent d p).1 = homogeneousComponent d p.1 :=
  rfl

theorem symmetricHomogeneousComponent_isHomogeneous (d : ℕ)
    (p : SymmetricRing k σ) :
    IsHomogeneous (symmetricHomogeneousComponent d p).1 d :=
  homogeneousComponent_isHomogeneous d p.1

/-- Taking a homogeneous component after multiplying on the right by a
homogeneous polynomial merely shifts the requested degree. -/
theorem homogeneousComponent_mul_right
    (p q : MvPolynomial σ k) (e t : ℕ)
    (hq : IsHomogeneous q e) :
    homogeneousComponent t (p * q) =
      if e ≤ t then homogeneousComponent (t - e) p * q else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
      have hp : IsHomogeneous (monomial u r : MvPolynomial σ k) u.degree :=
        isHomogeneous_monomial r rfl
      rw [homogeneousComponent_of_mem hp,
        homogeneousComponent_of_mem (hp.mul hq)]
      by_cases het : e ≤ t
      · simp only [if_pos het]
        by_cases hdeg : t - e = u.degree
        · have ht : t = u.degree + e := by omega
          simp [hdeg, ht]
        · have ht : t ≠ u.degree + e := by omega
          simp [hdeg, ht]
      · have ht : t ≠ u.degree + e := by omega
        simp [het, ht]
  | add p q hp hq' =>
      simp only [add_mul, map_add, hp, hq']
      split_ifs <;> simp

/-- Keep, in each symmetric coefficient, precisely the component which can
contribute to total degree `t` after multiplication by `b i`. -/
def degreeComponentFinsupp
    (degree : ι → ℕ) (t : ℕ)
    (c : ι →₀ SymmetricRing k σ) :
    ι →₀ SymmetricRing k σ :=
  Finsupp.onFinset c.support
    (fun i => if h : degree i ≤ t then
      symmetricHomogeneousComponent (t - degree i) (c i) else 0)
    (by
      intro i hi
      by_contra hic
      have hci : c i = 0 := Finsupp.notMem_support_iff.mp hic
      simp [hci] at hi)

def degreeComponentCoordinates
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ) (t : ℕ)
    (c : ι →₀ SymmetricRing k σ) :
    ι →₀ SymmetricRing k σ :=
  degreeComponentFinsupp degree t c

@[simp]
theorem degreeComponentFinsupp_apply
    (degree : ι → ℕ) (t : ℕ)
    (c : ι →₀ SymmetricRing k σ) (i : ι) :
    degreeComponentFinsupp degree t c i =
      if h : degree i ≤ t then
        symmetricHomogeneousComponent (t - degree i) (c i) else 0 := by
  simp [degreeComponentFinsupp]

@[simp]
theorem degreeComponentCoordinates_apply
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ) (t : ℕ)
    (c : ι →₀ SymmetricRing k σ) (i : ι) :
    degreeComponentCoordinates b degree t c i =
      if h : degree i ≤ t then
        symmetricHomogeneousComponent (t - degree i) (c i) else 0 := by
  simp [degreeComponentCoordinates]

/-- Family form of homogeneous coefficient extraction.  Linear independence
is not needed for this identity. -/
theorem homogeneousComponent_linearCombination_family
    (v : ι → PolynomialRing k σ) (degree : ι → ℕ)
    (hv : ∀ i, IsHomogeneous (v i) (degree i))
    (t : ℕ) (c : ι →₀ SymmetricRing k σ) :
    homogeneousComponent t
        (Finsupp.linearCombination (SymmetricRing k σ) v c) =
      Finsupp.linearCombination (SymmetricRing k σ) v
        (degreeComponentFinsupp degree t c) := by
  classical
  rw [Finsupp.linearCombination_apply]
  change homogeneousComponent t
    (c.support.sum fun i => (c i).1 * v i) = _
  rw [map_sum]
  have hsupp : degreeComponentFinsupp degree t c ∈
      Finsupp.supported (SymmetricRing k σ) (SymmetricRing k σ)
        (↑c.support : Set ι) := by
    apply (Finsupp.mem_supported' (SymmetricRing k σ) _).2
    intro i hi
    have hci : c i = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa using hi
    simp [degreeComponentFinsupp_apply, hci]
  rw [Finsupp.linearCombination_apply_of_mem_supported
    (SymmetricRing k σ) hsupp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [degreeComponentFinsupp_apply]
  by_cases hit : degree i ≤ t
  · simp only [dif_pos hit]
    change homogeneousComponent t ((c i).1 * v i) =
      (symmetricHomogeneousComponent (t - degree i) (c i)).1 * v i
    simpa [hit] using homogeneousComponent_mul_right
      (c i).1 (v i) (degree i) t (hv i)
  · simp only [dif_neg hit]
    change homogeneousComponent t ((c i).1 * v i) = 0
    simpa [hit] using homogeneousComponent_mul_right
      (c i).1 (v i) (degree i) t (hv i)

/-- Homogeneous components can be computed coefficientwise in a homogeneous
basis, with the degree shift dictated by the basis vector. -/
theorem homogeneousComponent_linearCombination
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    (t : ℕ) (c : ι →₀ SymmetricRing k σ) :
    homogeneousComponent t
        (Finsupp.linearCombination (SymmetricRing k σ) b c) =
      Finsupp.linearCombination (SymmetricRing k σ) b
        (degreeComponentCoordinates b degree t c) := by
  classical
  rw [Finsupp.linearCombination_apply]
  change homogeneousComponent t
    (c.support.sum fun i => (c i).1 * b i) = _
  rw [map_sum]
  have hsupp : degreeComponentCoordinates b degree t c ∈
      Finsupp.supported (SymmetricRing k σ) (SymmetricRing k σ)
        (↑c.support : Set ι) := by
    apply (Finsupp.mem_supported' (SymmetricRing k σ) _).2
    intro i hi
    have hci : c i = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa using hi
    simp [degreeComponentCoordinates_apply, hci]
  rw [Finsupp.linearCombination_apply_of_mem_supported
    (SymmetricRing k σ) hsupp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [degreeComponentCoordinates_apply]
  by_cases hit : degree i ≤ t
  · simp only [dif_pos hit]
    change homogeneousComponent t ((c i).1 * b i) =
      (symmetricHomogeneousComponent (t - degree i) (c i)).1 * b i
    simpa [hit] using homogeneousComponent_mul_right
      (c i).1 (b i) (degree i) t (hb i)
  · simp only [dif_neg hit]
    change homogeneousComponent t ((c i).1 * b i) = 0
    simpa [hit] using homogeneousComponent_mul_right
      (c i).1 (b i) (degree i) t (hb i)

/-- The coordinate formula for one homogeneous component. -/
theorem repr_homogeneousComponent_apply
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    (p : PolynomialRing k σ) (t : ℕ) (i : ι) :
    b.repr (homogeneousComponent t p) i =
      if h : degree i ≤ t then
        symmetricHomogeneousComponent (t - degree i) (b.repr p i)
      else 0 := by
  have hcomponent := homogeneousComponent_linearCombination
    b degree hb t (b.repr p)
  rw [b.linearCombination_repr] at hcomponent
  rw [hcomponent, b.repr_linearCombination]
  exact degreeComponentCoordinates_apply b degree t (b.repr p) i

/-- A coordinate above the degree of a homogeneous vector is zero.  This is
the triangularity assertion needed for the Reynolds matrix. -/
theorem repr_eq_zero_of_degree_lt
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    {p : PolynomialRing k σ} {d : ℕ}
    (hp : IsHomogeneous p d) (i : ι) (hdi : d < degree i) :
    b.repr p i = 0 := by
  have h := repr_homogeneousComponent_apply b degree hb p d i
  rw [homogeneousComponent_eq_self hp] at h
  simpa [Nat.not_le_of_gt hdi] using h

/-- Every surviving coordinate has the unique shifted homogeneous degree. -/
theorem repr_isHomogeneous
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    {p : PolynomialRing k σ} {d : ℕ}
    (hp : IsHomogeneous p d) (i : ι) (hid : degree i ≤ d) :
    IsHomogeneous (b.repr p i).1 (d - degree i) := by
  have h := repr_homogeneousComponent_apply b degree hb p d i
  rw [homogeneousComponent_eq_self hp, dif_pos hid] at h
  rw [h]
  exact symmetricHomogeneousComponent_isHomogeneous
    (d - degree i) (b.repr p i)

/-- Projection onto an arbitrary subset of a homogeneous basis.  Although it
is only linear over the symmetric coefficient ring, it preserves ordinary
polynomial homogeneity because every retained coordinate has the uniquely
shifted degree proved above. -/
def basisCoordinateProjection
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (keep : ι → Prop) [DecidablePred keep] :
    PolynomialRing k σ →ₗ[SymmetricRing k σ] PolynomialRing k σ where
  toFun p := b.repr.symm ((b.repr p).filter keep)
  map_add' p q := by
    apply b.repr.injective
    simp
  map_smul' r p := by
    apply b.repr.injective
    simp

theorem basisCoordinateProjection_apply
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (keep : ι → Prop) [DecidablePred keep]
    (p : PolynomialRing k σ) :
    basisCoordinateProjection b keep p =
      Finsupp.linearCombination (SymmetricRing k σ) b
        ((b.repr p).filter keep) := by
  simp [basisCoordinateProjection]

/-- Every coordinate-subset projection associated with a homogeneous basis
preserves homogeneity. -/
theorem basisCoordinateProjection_preserves_homogeneous
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    (keep : ι → Prop) [DecidablePred keep]
    {p : PolynomialRing k σ} {d : ℕ} (hp : IsHomogeneous p d) :
    IsHomogeneous (basisCoordinateProjection b keep p) d := by
  classical
  rw [basisCoordinateProjection_apply]
  rw [Finsupp.linearCombination_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  change IsHomogeneous (((b.repr p).filter keep i).1 * b i) d
  by_cases hkeep : keep i
  · rw [Finsupp.filter_apply_pos _ _ hkeep]
    by_cases hid : degree i ≤ d
    · have hc := repr_isHomogeneous b degree hb hp i hid
      simpa [Nat.sub_add_cancel hid] using hc.mul (hb i)
    · have hc := repr_eq_zero_of_degree_lt b degree hb hp i
        (Nat.lt_of_not_ge hid)
      simp [hc, MvPolynomial.isHomogeneous_zero]
  · rw [Finsupp.filter_apply_neg _ _ hkeep]
    exact MvPolynomial.isHomogeneous_zero σ k d

section EmbeddedBasis

variable {N : Type*} [AddCommGroup N]
variable [Module (SymmetricRing k σ) N]

/-- Coordinate projection for a homogeneous basis of a module embedded in the
polynomial ring. -/
def embeddedBasisCoordinateProjection
    (b : Module.Basis ι (SymmetricRing k σ) N)
    (keep : ι → Prop) [DecidablePred keep] :
    N →ₗ[SymmetricRing k σ] N where
  toFun x := b.repr.symm ((b.repr x).filter keep)
  map_add' x y := by
    apply b.repr.injective
    simp
  map_smul' a x := by
    apply b.repr.injective
    simp

@[simp]
theorem embeddedBasisCoordinateProjection_repr
    (b : Module.Basis ι (SymmetricRing k σ) N)
    (keep : ι → Prop) [DecidablePred keep] (x : N) :
    b.repr (embeddedBasisCoordinateProjection b keep x) =
      (b.repr x).filter keep := by
  simp [embeddedBasisCoordinateProjection]

/-- The shifted-coordinate argument only needs an injective realization of
the free module inside the polynomial ring. -/
theorem embedded_repr_isHomogeneous
    (b : Module.Basis ι (SymmetricRing k σ) N)
    (realize : N →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (hrealize : Function.Injective realize)
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (realize (b i)) (degree i))
    {x : N} {d : ℕ} (hx : IsHomogeneous (realize x) d)
    (i : ι) (hid : degree i ≤ d) :
    IsHomogeneous (b.repr x i).1 (d - degree i) := by
  let c := b.repr x
  let c' := degreeComponentFinsupp degree d c
  have hsum : realize x =
      Finsupp.linearCombination (SymmetricRing k σ)
        (fun i => realize (b i)) c := by
    rw [← b.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
    rfl
  have hcomponent : realize x =
      Finsupp.linearCombination (SymmetricRing k σ)
        (fun i => realize (b i)) c' := by
    rw [← homogeneousComponent_eq_self hx, hsum]
    exact homogeneousComponent_linearCombination_family
      (fun i => realize (b i)) degree hb d c
  have hc : c = c' := by
    apply b.linearIndependent
    apply hrealize
    simpa only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
      using hsum.symm.trans hcomponent
  have hi := DFunLike.congr_fun hc i
  rw [degreeComponentFinsupp_apply, dif_pos hid] at hi
  rw [hi]
  exact symmetricHomogeneousComponent_isHomogeneous
    (d - degree i) (c i)

theorem embedded_repr_eq_zero_of_degree_lt
    (b : Module.Basis ι (SymmetricRing k σ) N)
    (realize : N →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (hrealize : Function.Injective realize)
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (realize (b i)) (degree i))
    {x : N} {d : ℕ} (hx : IsHomogeneous (realize x) d)
    (i : ι) (hdi : d < degree i) :
    b.repr x i = 0 := by
  let c := b.repr x
  let c' := degreeComponentFinsupp degree d c
  have hsum : realize x =
      Finsupp.linearCombination (SymmetricRing k σ)
        (fun i => realize (b i)) c := by
    rw [← b.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
    rfl
  have hcomponent : realize x =
      Finsupp.linearCombination (SymmetricRing k σ)
        (fun i => realize (b i)) c' := by
    rw [← homogeneousComponent_eq_self hx, hsum]
    exact homogeneousComponent_linearCombination_family
      (fun i => realize (b i)) degree hb d c
  have hc : c = c' := by
    apply b.linearIndependent
    apply hrealize
    simpa only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
      using hsum.symm.trans hcomponent
  have hi := DFunLike.congr_fun hc i
  rw [degreeComponentFinsupp_apply, dif_neg (Nat.not_le_of_gt hdi)] at hi
  exact hi

/-- Coordinate projection remains homogeneous after any injective homogeneous
realization into the polynomial ring. -/
theorem embeddedBasisCoordinateProjection_preserves_homogeneous
    (b : Module.Basis ι (SymmetricRing k σ) N)
    (realize : N →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (hrealize : Function.Injective realize)
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (realize (b i)) (degree i))
    (keep : ι → Prop) [DecidablePred keep]
    {x : N} {d : ℕ} (hx : IsHomogeneous (realize x) d) :
    IsHomogeneous
      (realize (embeddedBasisCoordinateProjection b keep x)) d := by
  classical
  change IsHomogeneous
    (realize (b.repr.symm ((b.repr x).filter keep))) d
  rw [b.repr_symm_apply]
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  by_cases hkeep : keep i
  · rw [Finsupp.filter_apply_pos _ _ hkeep]
    by_cases hid : degree i ≤ d
    · have hc := embedded_repr_isHomogeneous b realize hrealize
        degree hb hx i hid
      change IsHomogeneous ((b.repr x i).1 * realize (b i)) d
      simpa [Nat.sub_add_cancel hid] using hc.mul (hb i)
    · have hc := embedded_repr_eq_zero_of_degree_lt b realize hrealize
        degree hb hx i (Nat.lt_of_not_ge hid)
      simp [hc, MvPolynomial.isHomogeneous_zero]
  · rw [Finsupp.filter_apply_neg _ _ hkeep]
    exact MvPolynomial.isHomogeneous_zero σ k d

end EmbeddedBasis

/-- A degree-preserving endomorphism has no matrix entry from a lower-degree
basis vector to a higher-degree basis vector. -/
theorem matrixEntry_eq_zero_of_degree_lt
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    (p : PolynomialRing k σ →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (hp : ∀ {q : PolynomialRing k σ} {d : ℕ},
      IsHomogeneous q d → IsHomogeneous (p q) d)
    (i j : ι) (hij : degree j < degree i) :
    b.repr (p (b j)) i = 0 :=
  repr_eq_zero_of_degree_lt b degree hb (hp (hb j)) i hij

/-- An equal-degree matrix entry of a degree-preserving map is homogeneous of
degree zero. -/
theorem matrixEntry_isHomogeneous_zero
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    (p : PolynomialRing k σ →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (hp : ∀ {q : PolynomialRing k σ} {d : ℕ},
      IsHomogeneous q d → IsHomogeneous (p q) d)
    (i j : ι) (hij : degree i = degree j) :
    IsHomogeneous (b.repr (p (b j)) i).1 0 := by
  have h := repr_isHomogeneous b degree hb (hp (hb j)) i
    (by omega : degree i ≤ degree j)
  simpa [hij] using h

/-- Thus every equal-degree matrix entry is literally a ground-field scalar,
not merely an arbitrary symmetric polynomial. -/
theorem exists_matrixEntry_eq_algebraMap
    (b : Module.Basis ι (SymmetricRing k σ) (PolynomialRing k σ))
    (degree : ι → ℕ)
    (hb : ∀ i, IsHomogeneous (b i) (degree i))
    (p : PolynomialRing k σ →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (hp : ∀ {q : PolynomialRing k σ} {d : ℕ},
      IsHomogeneous q d → IsHomogeneous (p q) d)
    (i j : ι) (hij : degree i = degree j) :
    ∃ r : k, b.repr (p (b j)) i = algebraMap k (SymmetricRing k σ) r := by
  let c := b.repr (p (b j)) i
  have hc : IsHomogeneous c.1 0 :=
    matrixEntry_isHomogeneous_zero b degree hb p hp i j hij
  refine ⟨coeff 0 c.1, ?_⟩
  apply Subtype.ext
  change c.1 = C (coeff 0 c.1)
  exact totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous σ).mpr hc)

end

end LeanProofs.PolynomialFormulas.LazardInvariantHomogeneousCoordinates
