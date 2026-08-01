import PolynomialFormulas.FrobeniusDummitResolvent
import PolynomialFormulas.QuinticRadicalPrimrec
import PolynomialFormulas.QuinticScalarGaloisBridge

/-!
# Abstract coefficients of the Frobenius--Dummit sextic

The universal scalar resolvent has coefficients that are fixed polynomials in
the five elementary symmetric functions. This file selects those polynomials
with the fundamental theorem of symmetric polynomials, evaluates them at the
signed coefficients of a monic integral quintic, and proves the resulting
seven-coefficient function primitive recursive. The separate certified sparse
table supplies the directly evaluable implementation.
-/

open MvPolynomial Polynomial

set_option maxHeartbeats 1000000

namespace LeanProofs.PolynomialFormulas.QuinticDummitCoefficients

open FrobeniusDummitResolvent
open QuinticRadicalDecidability
open QuinticRadicalDecidability.MonicQuintic
open QuinticRadicalPrimrec
open QuinticScalarGaloisBridge

/-- The elementary symmetric functions of the roots of
`X⁵ + B X⁴ + C X³ + D X² + E X + H`, in increasing order. -/
def elementaryCoefficients (f : MonicQuintic) : Fin 5 → ℤ :=
  ![-f.B, f.C, -f.D, f.E, -f.H]

theorem elementaryCoefficients_apply_primrec (i : Fin 5) :
    Primrec fun f : MonicQuintic ↦ elementaryCoefficients f i := by
  fin_cases i
  · simpa [elementaryCoefficients] using
      (int_neg_primrec.comp monicQuintic_B_primrec).of_eq (fun f ↦ by rfl)
  · simpa [elementaryCoefficients] using monicQuintic_C_primrec
  · simpa [elementaryCoefficients] using
      (int_neg_primrec.comp monicQuintic_D_primrec).of_eq (fun f ↦ by rfl)
  · simpa [elementaryCoefficients] using monicQuintic_E_primrec
  · simpa [elementaryCoefficients] using
      (int_neg_primrec.comp monicQuintic_H_primrec).of_eq (fun f ↦ by rfl)

/-- Evaluating any *fixed* integer multivariate polynomial at the elementary
coefficient tuple is primitive recursive.  This lemma isolates the reusable
computability argument behind all seven resolvent coefficients. -/
theorem eval₂_elementaryCoefficients_primrec
    (q : MvPolynomial (Fin 5) ℤ) :
    Primrec fun f : MonicQuintic ↦
      MvPolynomial.eval₂ (Int.castRingHom ℤ) (elementaryCoefficients f) q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      simpa using (Primrec.const a : Primrec fun _ : MonicQuintic ↦ a)
  | add p q hp hq =>
      simpa [MvPolynomial.eval₂_add] using int_add_primrec.comp hp hq
  | mul_X p i hp =>
      simpa [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
        int_mul_primrec.comp hp (elementaryCoefficients_apply_primrec i)

/-- The seven integral coefficients, in ascending degree order, of the
Frobenius--Dummit sextic attached to a monic integral quintic. -/
noncomputable def dummitCoefficients (f : MonicQuintic) : IntegerSextic :=
  fun n ↦ MvPolynomial.eval₂ (Int.castRingHom ℤ) (elementaryCoefficients f)
    (elementaryResolventCoefficient n)

theorem dummitCoefficients_apply_primrec (n : Fin 7) :
    Primrec fun f : MonicQuintic ↦ dummitCoefficients f n :=
  eval₂_elementaryCoefficients_primrec (elementaryResolventCoefficient n)

/-- Although the coefficient polynomials are selected once and for all via
the fundamental theorem of symmetric polynomials, their joint evaluation is
an actual primitive-recursive function. -/
theorem dummitCoefficients_primrec : Primrec dummitCoefficients := by
  apply Primrec.fin_curry.mpr
  have h : Primrec₂ fun n : Fin 7 ↦ fun f : MonicQuintic ↦
      dummitCoefficients f n :=
    Primrec.fin_curry₁.mpr dummitCoefficients_apply_primrec
  exact h.swap

theorem elementaryResolventCoefficient_six :
    elementaryResolventCoefficient 6 = 1 := by
  apply (MvPolynomial.esymmAlgEquiv (Fin 5) ℤ (by simp)).injective
  rw [esymmAlgEquiv_elementaryResolventCoefficient]
  apply Subtype.ext
  simp only [symmetricResolventCoefficient, map_one]
  change universalResolvent.coeff 6 = (1 : MvPolynomial (Fin 5) ℤ)
  simpa only [universalResolvent_natDegree] using
    universalResolvent_monic.coeff_natDegree

@[simp] theorem dummitCoefficients_six (f : MonicQuintic) :
    dummitCoefficients f 6 = 1 := by
  simp [dummitCoefficients, elementaryResolventCoefficient_six]

/-! ## Specialization -/

/-- Evaluation commutes with replacing the elementary symmetric functions by
their values.  This is the reusable algebraic core of coefficient
specialization. -/
theorem eval₂_elementaryResolventCoefficient_specialize
    {K : Type*} [CommRing K] (f : MonicQuintic) (r : Fin 5 → K)
    (hesymm : ∀ i : Fin 5,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) =
        (elementaryCoefficients f i : K))
    (q : MvPolynomial (Fin 5) ℤ) :
    Int.castRingHom K
        (MvPolynomial.eval₂ (Int.castRingHom ℤ)
          (elementaryCoefficients f) q) =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1)) q) := by
  change _ = (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
    (MvPolynomial.aeval
      (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1)) q)
  rw [MvPolynomial.map_aeval]
  rw [show (MvPolynomial.eval₂Hom (Int.castRingHom K) r).comp
      (algebraMap ℤ (MvPolynomial (Fin 5) ℤ)) = Int.castRingHom K by
    ext z
    simp]
  change _ = MvPolynomial.eval₂ (Int.castRingHom K)
    (fun i : Fin 5 ↦ MvPolynomial.eval₂ (Int.castRingHom K) r
      (MvPolynomial.esymm (Fin 5) ℤ (i + 1))) q
  rw [MvPolynomial.eval₂_comp_left (Int.castRingHom K)
    (Int.castRingHom ℤ) (elementaryCoefficients f) q]
  rw [show (Int.castRingHom K).comp (Int.castRingHom ℤ) =
      Int.castRingHom K by
    ext z
    simp]
  apply congrArg (fun s : Fin 5 → K ↦
    MvPolynomial.eval₂ (Int.castRingHom K) s q)
  funext i
  exact (hesymm i).symm

/-- Under the elementary-symmetric hypothesis, each selected integer
coefficient is the corresponding coefficient of the scalar resolvent. -/
theorem dummitCoefficients_cast_eq_scalarResolvent_coeff
    {K : Type*} [CommRing K] (f : MonicQuintic) (r : Fin 5 → K)
    (hesymm : ∀ i : Fin 5,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) =
        (elementaryCoefficients f i : K))
    (n : Fin 7) :
    Int.castRingHom K (dummitCoefficients f n) =
      (scalarResolvent r).coeff n := by
  rw [dummitCoefficients, scalarResolvent_coefficient_eq]
  exact eval₂_elementaryResolventCoefficient_specialize f r hesymm _

/-- A degree-at-most-six polynomial is determined by its first seven
coefficients.  This form is tailored to the executable `IntegerSextic`
representation. -/
theorem integerSextic_polynomial_map_eq_of_coeff
    {K : Type*} [CommRing K] (A : IntegerSextic) (P : K[X])
    (hP : P.natDegree ≤ 6)
    (hcoeff : ∀ i : Fin 7, (A i : K) = P.coeff i) :
    A.polynomial.map (Int.castRingHom K) = P := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp only [IntegerSextic.polynomial, Polynomial.coeff_map,
        Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C] <;>
      norm_num at *
    all_goals exact hcoeff _
  · have hn' : 6 < n := by omega
    have hp0 : P.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hn')
    rw [hp0]
    simp only [IntegerSextic.polynomial, Polynomial.coeff_map,
      Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega]

/-- The selected integral sextic specializes to the actual scalar
Frobenius--Dummit resolvent whenever the five elementary symmetric values are
the signed coefficients of the monic quintic. -/
theorem dummitPolynomial_map_eq_scalarResolvent
    {K : Type*} [CommRing K] (f : MonicQuintic) (r : Fin 5 → K)
    (hesymm : ∀ i : Fin 5,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) =
        (elementaryCoefficients f i : K)) :
    (dummitCoefficients f).polynomial.map (Int.castRingHom K) =
      scalarResolvent r := by
  apply integerSextic_polynomial_map_eq_of_coeff
  · calc
      (scalarResolvent r).natDegree ≤ universalResolvent.natDegree :=
        Polynomial.natDegree_map_le
      _ = 6 := universalResolvent_natDegree
  · exact dummitCoefficients_cast_eq_scalarResolvent_coeff f r hesymm

/-! ## The elementary-symmetric hypothesis for an ordered root tuple -/

/-- Vieta's formula for the chosen ordering of the five roots in the canonical
splitting field. -/
theorem esymm_rootTuple {p : ℚ[X]} (hp : Irreducible p)
    (hmonic : p.Monic) (hdeg : p.natDegree = 5) (j : ℕ) (hj : j ≤ 5) :
    (Finset.univ.val.map (rootTuple p hp hdeg)).esymm j =
      (-1) ^ j *
        (p.map (algebraMap ℚ p.SplittingField)).coeff (5 - j) := by
  have hprod := mapped_eq_prod_rootTuple p hp hmonic hdeg
  have hc := congrArg (fun q : p.SplittingField[X] ↦ q.coeff (5 - j)) hprod
  rw [Finset.prod] at hc
  change _ =
    (((Finset.univ.val.map (rootTuple p hp hdeg)).map
      fun t ↦ Polynomial.X - Polynomial.C t).prod).coeff (5 - j) at hc
  rw [Multiset.prod_X_sub_C_coeff] at hc
  · rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ,
      Fintype.card_fin, Nat.sub_sub_self hj] at hc
    rw [hc, ← mul_assoc, ← pow_add, show j + j = 2 * j by omega, pow_mul]
    norm_num
  · simp

/-- The rational monic quintic associated to an executable monic integral
quintic. -/
noncomputable def monicQuinticRatPolynomial (f : MonicQuintic) : ℚ[X] :=
  f.polynomial.map (Int.castRingHom ℚ)

theorem monicQuinticRatPolynomial_monic (f : MonicQuintic) :
    (monicQuinticRatPolynomial f).Monic :=
  f.polynomial_monic.map _

@[simp] theorem monicQuinticRatPolynomial_natDegree (f : MonicQuintic) :
    (monicQuinticRatPolynomial f).natDegree = 5 := by
  rw [monicQuinticRatPolynomial, f.polynomial_monic.natDegree_map,
    f.polynomial_natDegree]

/-- The five signed coefficients are exactly the coefficient form of Vieta's
formula over any target commutative ring. -/
theorem signed_monicQuintic_coefficient {K : Type*} [CommRing K]
    (f : MonicQuintic) (i : Fin 5) :
    (-1 : K) ^ ((i : ℕ) + 1) *
        (f.polynomial.map (Int.castRingHom K)).coeff
          (5 - ((i : ℕ) + 1)) =
      (elementaryCoefficients f i : K) := by
  fin_cases i <;>
    simp only [elementaryCoefficients, MonicQuintic.polynomial,
      Polynomial.coeff_map, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C] <;>
    norm_num

/-- Vieta discharges the elementary-symmetric hypothesis for the chosen
enumeration of the roots of an irreducible monic quintic. -/
theorem rootTuple_esymm_eq_elementaryCoefficients
    (f : MonicQuintic)
    (hp : Irreducible (monicQuinticRatPolynomial f)) (i : Fin 5) :
    MvPolynomial.eval₂
        (Int.castRingHom (monicQuinticRatPolynomial f).SplittingField)
        (rootTuple (monicQuinticRatPolynomial f) hp
          (monicQuinticRatPolynomial_natDegree f))
        (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) =
      (elementaryCoefficients f i :
        (monicQuinticRatPolynomial f).SplittingField) := by
  let p : ℚ[X] := monicQuinticRatPolynomial f
  have hdeg : p.natDegree = 5 := monicQuinticRatPolynomial_natDegree f
  have he := esymm_rootTuple hp (monicQuinticRatPolynomial_monic f)
    hdeg (i + 1) (by omega)
  have hmap :
      p.map (algebraMap ℚ p.SplittingField) =
        f.polynomial.map (Int.castRingHom p.SplittingField) := by
    dsimp only [p, monicQuinticRatPolynomial]
    rw [Polynomial.map_map]
    congr 1
  have haeval :
      MvPolynomial.aeval
          (rootTuple p hp hdeg)
          (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) =
        algebraMap ℤ p.SplittingField (elementaryCoefficients f i) := by
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    rw [he, hmap]
    exact signed_monicQuintic_coefficient f i
  rw [MvPolynomial.aeval_def] at haeval
  convert haeval using 1
  · change MvPolynomial.eval₂ (Int.castRingHom p.SplittingField)
        (rootTuple p hp hdeg) (MvPolynomial.esymm (Fin 5) ℤ (i + 1)) =
      MvPolynomial.eval₂ (algebraMap ℤ p.SplittingField)
        (rootTuple p hp hdeg) (MvPolynomial.esymm (Fin 5) ℤ (i + 1))
    rw [RingHom.eq_intCast' (algebraMap ℤ p.SplittingField)]
  · change Int.castRingHom p.SplittingField (elementaryCoefficients f i) =
      algebraMap ℤ p.SplittingField (elementaryCoefficients f i)
    rw [RingHom.eq_intCast' (algebraMap ℤ p.SplittingField)]

/-- The abstract integer sextic is the scalar resolvent of the chosen ordered
root tuple. -/
theorem dummitPolynomial_map_eq_scalarResolvent_rootTuple
    (f : MonicQuintic)
    (hp : Irreducible (monicQuinticRatPolynomial f)) :
    (dummitCoefficients f).polynomial.map
        (Int.castRingHom (monicQuinticRatPolynomial f).SplittingField) =
      scalarResolvent
        (rootTuple (monicQuinticRatPolynomial f) hp
          (monicQuinticRatPolynomial_natDegree f)) := by
  apply dummitPolynomial_map_eq_scalarResolvent
  exact rootTuple_esymm_eq_elementaryCoefficients f hp

end LeanProofs.PolynomialFormulas.QuinticDummitCoefficients
