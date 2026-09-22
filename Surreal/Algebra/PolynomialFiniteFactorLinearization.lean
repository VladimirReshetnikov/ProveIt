import Surreal.Algebra.PolynomialFactorLinearization
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Finite coprime-factor linearization

This is the full finite-family isomorphism `polynomial:eq:factorlinear`
in `docs/surcomplex/polynomial-algebra/article.tex`. Each correction has
degree below its corresponding monic factor, and their cofactor-weighted
sum realizes an arbitrary polynomial below the total degree, uniquely.

The proof uses the binary Sylvester inverse for each factor and its
cofactor. Pairwise coprimality combines the local congruences; the degree
bound turns congruence modulo the full product into exact equality. It
works over any commutative coefficient ring, allows degree-zero factors,
and includes the empty family. No infinite Hensel lift is asserted.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι]

local instance finiteFactorDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The product of every factor except the selected one. -/
def factorCofactor (p : ι → R[X]) (i : ι) : R[X] :=
  ∏ j ∈ Finset.univ.erase i, p j

/-- The coefficient of first order in the product perturbation. -/
def factorLinearSum (p h : ι → R[X]) : R[X] :=
  ∑ i, h i * factorCofactor p i

/-- Degree control for one cofactor-weighted perturbation. -/
theorem degree_mul_factorCofactor_lt (p h : ι → R[X]) (i : ι)
    (hh : (h i).degree < (p i).natDegree) :
    (h i * factorCofactor p i).degree < (∑ j, (p j).natDegree : ℕ) := by
  by_cases hzero : h i = 0
  · rw [hzero, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  have hd := (natDegree_lt_iff_degree_lt hzero).mpr hh
  have hc : (factorCofactor p i).natDegree ≤
      ∑ j ∈ Finset.univ.erase i, (p j).natDegree := natDegree_prod_le _ _
  have hsum : (p i).natDegree + (∑ j ∈ Finset.univ.erase i, (p j).natDegree) =
      ∑ j, (p j).natDegree :=
    Finset.add_sum_erase _ (fun j => (p j).natDegree) (Finset.mem_univ i)
  exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr
    (natDegree_mul_le.trans_lt ((Nat.add_lt_add_of_lt_of_le hd hc).trans_eq hsum)))

/-- A sum of bounded factor perturbations is below the total degree,
including when the index type is empty. -/
theorem degree_factorLinearSum_lt (p h : ι → R[X])
    (hh : ∀ i, (h i).degree < (p i).natDegree) :
    (factorLinearSum p h).degree < (∑ i, (p i).natDegree : ℕ) := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro i _
  exact degree_mul_factorCofactor_lt p h i (hh i)

/-- The factor and its cofactor remain coprime. -/
theorem isCoprime_factorCofactor (p : ι → R[X])
    (hp : Pairwise fun i j => IsCoprime (p i) (p j)) (i : ι) :
    IsCoprime (p i) (factorCofactor p i) := by
  apply IsCoprime.prod_right
  intro j hj
  exact hp (Finset.mem_erase.mp hj).1.symm

/-- An off-diagonal cofactor contains the selected factor. -/
theorem factor_dvd_factorCofactor (p : ι → R[X]) {i j : ι} (hij : i ≠ j) :
    p i ∣ factorCofactor p j :=
  Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

/-- Reduction modulo a factor retains just its own perturbation term. -/
theorem factor_dvd_linearSum_sub_term (p h : ι → R[X]) (i : ι) :
    p i ∣ factorLinearSum p h - h i * factorCofactor p i := by
  unfold factorLinearSum
  rw [← Finset.sum_erase_add _ (fun j => h j * factorCofactor p j) (Finset.mem_univ i),
    add_sub_cancel_right]
  apply Finset.dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_right
    (factor_dvd_factorCofactor p (Finset.mem_erase.mp hj).1.symm) _

private theorem eq_zero_of_monic_dvd_of_degree_lt {p f : R[X]} (hp : p.Monic)
    (hf : f.degree < p.natDegree) (hdiv : p ∣ f) : f = 0 := by
  nontriviality R
  have hd : f.degree < p.degree := by rwa [degree_eq_natDegree hp.ne_zero]
  calc
    f = f %ₘ p := ((modByMonic_eq_self_iff hp).mpr hd).symm
    _ = 0 := (modByMonic_eq_zero_iff_dvd hp).mpr hdiv

/-- Bounded corrections are uniquely determined by their linearized product. -/
theorem factorLinearSum_injective_on_bounds (p : ι → R[X])
    (hm : ∀ i, (p i).Monic) (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    {h k : ι → R[X]} (hh : ∀ i, (h i).degree < (p i).natDegree)
    (hk : ∀ i, (k i).degree < (p i).natDegree)
    (heq : factorLinearSum p h = factorLinearSum p k) : h = k := by
  funext i
  have hdiv : p i ∣ (h i - k i) * factorCofactor p i := by
    have hd := dvd_sub (factor_dvd_linearSum_sub_term p k i)
      (factor_dvd_linearSum_sub_term p h i)
    convert hd using 1
    rw [heq]
    ring
  apply sub_eq_zero.mp
  exact eq_zero_of_monic_dvd_of_degree_lt (hm i)
    (degree_sub_le _ _ |>.trans_lt (max_lt (hh i) (hk i)))
    ((isCoprime_factorCofactor p hp i).dvd_of_dvd_mul_right hdiv)

/-- The degrees of a monic factor and its cofactor add to the total degree. -/
theorem natDegree_factor_add_cofactor (p : ι → R[X])
    (hm : ∀ i, (p i).Monic) (i : ι) :
    (p i).natDegree + (factorCofactor p i).natDegree = ∑ j, (p j).natDegree := by
  rw [factorCofactor, natDegree_prod_of_monic _ _ (fun j _ => hm j)]
  exact Finset.add_sum_erase _ (fun j => (p j).natDegree) (Finset.mem_univ i)

/-- Every target below the total degree has bounded corrections. This
uses only binary coprime inverses and exact divisibility, without a field
or dimension argument. -/
theorem exists_bounded_finite_factor_correction (p : ι → R[X])
    (hm : ∀ i, (p i).Monic) (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    (f : R[X]) (hf : f.degree < (∑ i, (p i).natDegree : ℕ)) :
    ∃ h : ι → R[X], (∀ i, (h i).degree < (p i).natDegree) ∧ factorLinearSum p h = f := by
  let f' (i : ι) : degreeLT R ((p i).natDegree + (factorCofactor p i).natDegree) :=
    ⟨f, mem_degreeLT.mpr (by rwa [natDegree_factor_add_cofactor p hm i])⟩
  let c (i : ι) := factorCorrection (p i) (factorCofactor p i) (hm i)
    (isCoprime_factorCofactor p hp i) (f' i)
  let h (i : ι) : R[X] := (c i).1
  have hh : ∀ i, (h i).degree < (p i).natDegree :=
    fun i => mem_degreeLT.mp (c i).1.property
  refine ⟨h, hh, ?_⟩
  have hlocal (i : ι) : p i ∣ h i * factorCofactor p i - f := by
    have hc := factorCorrection_spec (p i) (factorCofactor p i) (hm i)
      (isCoprime_factorCofactor p hp i) (f' i)
    change h i * factorCofactor p i + p i * ((c i).2 : R[X]) = f at hc
    refine ⟨-((c i).2 : R[X]), ?_⟩
    rw [← hc]
    ring
  have hdiv : (∏ i, p i) ∣ factorLinearSum p h - f := by
    apply Fintype.prod_dvd_of_coprime hp
    intro i
    convert dvd_add (factor_dvd_linearSum_sub_term p h i) (hlocal i) using 1
    ring
  apply sub_eq_zero.mp
  apply eq_zero_of_monic_dvd_of_degree_lt (monic_prod_of_monic _ _ (fun i _ => hm i)) _ hdiv
  rw [natDegree_prod_of_monic _ _ (fun i _ => hm i)]
  exact (degree_sub_le _ _).trans_lt (max_lt (degree_factorLinearSum_lt p h hh) hf)

/-- The complete finite existence-and-uniqueness assertion of
`polynomial:eq:factorlinear`, including an empty family. -/
theorem existsUnique_bounded_finite_factor_correction (p : ι → R[X])
    (hm : ∀ i, (p i).Monic) (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    (f : R[X]) (hf : f.degree < (∑ i, (p i).natDegree : ℕ)) :
    ∃! h : ι → R[X], (∀ i, (h i).degree < (p i).natDegree) ∧ factorLinearSum p h = f := by
  obtain ⟨h, hh, heq⟩ := exists_bounded_finite_factor_correction p hm hp f hf
  refine ⟨h, ⟨hh, heq⟩, ?_⟩
  intro k hk
  exact factorLinearSum_injective_on_bounds p hm hp hk.1 hh (hk.2.trans heq.symm)

/-- The finite-family multiplication linearization on bounded polynomial modules. -/
def finiteFactorLinearMap (p : ι → R[X]) :
    ((i : ι) → degreeLT R (p i).natDegree) →ₗ[R]
      degreeLT R (∑ i, (p i).natDegree) where
  toFun h := ⟨factorLinearSum p (fun i => h i),
    mem_degreeLT.mpr (degree_factorLinearSum_lt p _ (fun i => mem_degreeLT.mp (h i).property))⟩
  map_add' h k := by
    apply Subtype.ext
    change (∑ i, ((h i : R[X]) + (k i : R[X])) * factorCofactor p i) = _
    simp only [add_mul, Finset.sum_add_distrib]
    rfl
  map_smul' a h := by
    apply Subtype.ext
    change (∑ i, (a • (h i : R[X])) * factorCofactor p i) = _
    simp only [smul_mul_assoc, ← Finset.smul_sum]
    rfl

@[simp] theorem finiteFactorLinearMap_apply (p : ι → R[X])
    (h : (i : ι) → degreeLT R (p i).natDegree) :
    (finiteFactorLinearMap p h : R[X]) = ∑ i, (h i : R[X]) * factorCofactor p i := rfl

/-- The finite-family isomorphism of `polynomial:eq:factorlinear`, over an
arbitrary commutative ring. Pairwise coprimality and monicity are the only
factor assumptions; no factor is required to have positive degree. -/
def finiteFactorLinearEquiv (p : ι → R[X]) (hm : ∀ i, (p i).Monic)
    (hp : Pairwise fun i j => IsCoprime (p i) (p j)) :
    ((i : ι) → degreeLT R (p i).natDegree) ≃ₗ[R]
      degreeLT R (∑ i, (p i).natDegree) :=
  LinearEquiv.ofBijective (finiteFactorLinearMap p) ⟨by
    intro h k heq
    have he : (fun i => (h i : R[X])) = (fun i => (k i : R[X])) :=
      factorLinearSum_injective_on_bounds p hm hp
        (fun i => mem_degreeLT.mp (h i).property) (fun i => mem_degreeLT.mp (k i).property)
        (congrArg (fun x : degreeLT R (∑ i, (p i).natDegree) => (x : R[X])) heq)
    funext i
    exact Subtype.ext (congrFun he i), by
    intro f
    obtain ⟨h, hh, heq⟩ := exists_bounded_finite_factor_correction p hm hp f
      (mem_degreeLT.mp f.property)
    exact ⟨fun i => ⟨h i, mem_degreeLT.mpr (hh i)⟩, Subtype.ext heq⟩⟩

@[simp] theorem finiteFactorLinearEquiv_apply (p : ι → R[X])
    (hm : ∀ i, (p i).Monic) (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    (h : (i : ι) → degreeLT R (p i).natDegree) :
    (finiteFactorLinearEquiv p hm hp h : R[X]) =
      ∑ i, (h i : R[X]) * factorCofactor p i := rfl

/-- The linear inverse supplying the bounded correction at each coefficient
stage of a later support-controlled factor lift. -/
def finiteFactorCorrection (p : ι → R[X]) (hm : ∀ i, (p i).Monic)
    (hp : Pairwise fun i j => IsCoprime (p i) (p j)) :
    degreeLT R (∑ i, (p i).natDegree) →ₗ[R]
      ((i : ι) → degreeLT R (p i).natDegree) :=
  (finiteFactorLinearEquiv p hm hp).symm.toLinearMap

/-- The inverse solves the exact cofactor sum equation. -/
theorem finiteFactorCorrection_spec (p : ι → R[X]) (hm : ∀ i, (p i).Monic)
    (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    (f : degreeLT R (∑ i, (p i).natDegree)) :
    factorLinearSum p (fun i => finiteFactorCorrection p hm hp f i) = (f : R[X]) :=
  congrArg (fun a : degreeLT R (∑ i, (p i).natDegree) => (a : R[X]))
    ((finiteFactorLinearEquiv p hm hp).apply_symm_apply f)

/-- Any bounded solution equals the one returned by the linear inverse. -/
theorem finiteFactorCorrection_unique (p : ι → R[X]) (hm : ∀ i, (p i).Monic)
    (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    (f : degreeLT R (∑ i, (p i).natDegree))
    (h : (i : ι) → degreeLT R (p i).natDegree)
    (heq : factorLinearSum p (fun i => h i) = (f : R[X])) :
    h = finiteFactorCorrection p hm hp f := by
  have hmap : finiteFactorLinearEquiv p hm hp h = f := Subtype.ext heq
  change h = (finiteFactorLinearEquiv p hm hp).symm f
  simpa only [LinearEquiv.symm_apply_apply] using
    congrArg (finiteFactorLinearEquiv p hm hp).symm hmap

end

end Surreal.FinitePolynomial
