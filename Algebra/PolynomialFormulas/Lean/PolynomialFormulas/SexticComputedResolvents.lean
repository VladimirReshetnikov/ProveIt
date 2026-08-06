import PolynomialFormulas.SexticSparseSymmetricSearch
import PolynomialFormulas.SexticDescriptorGaloisCriterion
import PolynomialFormulas.SexticRadicalDecidability

/-!
# Computed integral sextic resolvents

This file specializes the recursively discovered elementary-symmetric
coefficient formulas to the signed coefficients of a monic integral sextic.
The resulting finite integer lists are the executable degree-15 and degree-10
resolvents used by the eventual decision procedure.
-/

open scoped BigOperators
open MvPolynomial Polynomial

namespace LeanProofs.PolynomialFormulas.SexticComputedResolvents

open QuinticRadicalPrimrec
open SexticRadicalDecidability
open SexticRadicalDecidability.MonicSextic
open SexticScalarGaloisBridge
open SexticSeparatingInvariants
open SexticEvaluatedResolvents
open SexticSparseSymmetricSearch
open SexticSparseSymmetricSearch.SparsePolynomial

namespace SparseEvaluation

/-- Direct evaluation of one sparse term in six integer values. -/
def evalTerm (values : Fin 6 → ℤ) (t : SparseTerm) : ℤ :=
  t.coeff *
    values 0 ^ t.powers 0 * values 1 ^ t.powers 1 *
    values 2 ^ t.powers 2 * values 3 ^ t.powers 3 *
    values 4 ^ t.powers 4 * values 5 ^ t.powers 5

/-- Direct evaluation of a sparse polynomial. -/
def eval (values : Fin 6 → ℤ) : SparsePolynomial → ℤ
  | [] => 0
  | t :: p => evalTerm values t + eval values p

theorem cast_evalTerm {K : Type*} [CommRing K]
    (values : Fin 6 → ℤ) (t : SparseTerm) :
    (evalTerm values t : K) =
      MvPolynomial.eval₂ (Int.castRingHom K)
        (fun i ↦ (values i : K)) t.toMv := by
  rw [SparseTerm.toMv, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp [evalTerm, Fin.prod_univ_succ]
  ring

theorem cast_eval {K : Type*} [CommRing K]
    (values : Fin 6 → ℤ) (p : SparsePolynomial) :
    (eval values p : K) =
      MvPolynomial.eval₂ (Int.castRingHom K)
        (fun i ↦ (values i : K)) (SparsePolynomial.toMv p) := by
  induction p with
  | nil => simp [eval]
  | cons t p ih => simp [eval, cast_evalTerm, ih]

theorem int_pow_primrec : Primrec₂ ((· ^ ·) : ℤ → ℕ → ℤ) := by
  have hstep : Primrec₂ fun z : ℤ ↦ fun u : ℕ × ℤ ↦ u.2 * z := by
    change Primrec fun u : ℤ × (ℕ × ℤ) ↦ u.2.2 * u.1
    exact int_mul_primrec.comp
      (Primrec.snd.comp Primrec.snd) Primrec.fst
  exact (Primrec.nat_rec (Primrec.const 1) hstep).of_eq fun z n ↦ by
    induction n with
    | zero => simp
    | succ n ih => simp [ih, pow_succ]

theorem valuePow_primrec (i : Fin 6) :
    Primrec₂ fun values : Fin 6 → ℤ ↦
      fun t : SparseTerm ↦ values i ^ t.powers i := by
  change Primrec fun u : (Fin 6 → ℤ) × SparseTerm ↦
    u.1 i ^ u.2.powers i
  exact int_pow_primrec.comp
    (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
    (Primrec.fin_app.comp
      (SparsePolynomial.sparseTerm_powers_primrec.comp Primrec.snd)
      (Primrec.const i))

theorem evalTerm_primrec : Primrec₂ evalTerm := by
  change Primrec fun u : (Fin 6 → ℤ) × SparseTerm ↦ evalTerm u.1 u.2
  exact int_mul_primrec.comp
    (int_mul_primrec.comp
      (int_mul_primrec.comp
        (int_mul_primrec.comp
          (int_mul_primrec.comp
            (int_mul_primrec.comp
              (SparsePolynomial.sparseTerm_coeff_primrec.comp Primrec.snd)
              (valuePow_primrec 0))
            (valuePow_primrec 1))
          (valuePow_primrec 2))
        (valuePow_primrec 3))
      (valuePow_primrec 4))
    (valuePow_primrec 5)

theorem eval_primrec : Primrec₂ eval := by
  change Primrec fun u : (Fin 6 → ℤ) × SparsePolynomial ↦ eval u.1 u.2
  have hstep : Primrec₂ fun u : (Fin 6 → ℤ) × SparsePolynomial ↦
      fun v : SparseTerm × ℤ ↦ evalTerm u.1 v.1 + v.2 := by
    change Primrec fun u : ((Fin 6 → ℤ) × SparsePolynomial) ×
        (SparseTerm × ℤ) ↦
      evalTerm u.1.1 u.2.1 + u.2.2
    exact int_add_primrec.comp
      (evalTerm_primrec.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0)
    hstep).of_eq fun u ↦ by
      induction u.2 with
      | nil => rfl
      | cons t p ih => simp [eval, ih]

end SparseEvaluation

/-! ## Vieta values and executable coefficient lists -/

/-- The six elementary symmetric values prescribed by a monic sextic:
`e_(i+1) = (-1)^(i+1) b_(5-i)`. -/
def elementaryValues (f : MonicSextic) (i : Fin 6) : ℤ :=
  (-1) ^ ((i : ℕ) + 1) * f i.rev

theorem elementaryValues_apply_primrec (i : Fin 6) :
    Primrec fun f : MonicSextic ↦ elementaryValues f i := by
  exact int_mul_primrec.comp
    (Primrec.const ((-1 : ℤ) ^ ((i : ℕ) + 1)))
    (Primrec.fin_app.comp Primrec.id (Primrec.const i.rev))

theorem elementaryValues_primrec : Primrec elementaryValues := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.fin_curry₁.mpr elementaryValues_apply_primrec).swap

/-- Vieta's formula for the chosen ordering of six roots in the canonical
splitting field. -/
theorem sextic_esymm_rootTuple {p : ℚ[X]} (hp : Irreducible p)
    (hmonic : p.Monic) (hdeg : p.natDegree = 6) (j : ℕ) (hj : j ≤ 6) :
    (Finset.univ.val.map (rootTuple p hp hdeg)).esymm j =
      (-1) ^ j *
        (p.map (algebraMap ℚ p.SplittingField)).coeff (6 - j) := by
  have hprod := mapped_eq_prod_rootTuple p hp hmonic hdeg
  have hc := congrArg
    (fun q : p.SplittingField[X] ↦ q.coeff (6 - j)) hprod
  rw [Finset.prod] at hc
  change _ =
    (((Finset.univ.val.map (rootTuple p hp hdeg)).map
      fun t ↦ Polynomial.X - Polynomial.C t).prod).coeff (6 - j) at hc
  rw [Multiset.prod_X_sub_C_coeff] at hc
  · rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ,
      Fintype.card_fin, Nat.sub_sub_self hj] at hc
    calc
      (Finset.univ.val.map (rootTuple p hp hdeg)).esymm j =
          (-1) ^ j *
            ((-1) ^ j *
              (Finset.univ.val.map (rootTuple p hp hdeg)).esymm j) := by
        rw [← mul_assoc, ← pow_add,
          show j + j = 2 * j by omega, pow_mul]
        norm_num
      _ = (-1) ^ j *
          (p.map (algebraMap ℚ p.SplittingField)).coeff (6 - j) := by
        rw [← hc]
        rfl
  · simp

/-- Reading the six nonleading coefficients in reverse order. -/
theorem monicSextic_polynomial_coeff_rev (f : MonicSextic) (i : Fin 6) :
    f.polynomial.coeff (6 - ((i : ℕ) + 1)) = f i.rev := by
  fin_cases i <;>
    simp only [MonicSextic.polynomial, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C] <;>
    norm_num [Fin.rev] <;> congr 1

/-- The signed coefficient form of Vieta for an executable monic sextic. -/
theorem signed_monicSextic_coefficient {K : Type*} [CommRing K]
    (f : MonicSextic) (i : Fin 6) :
    (-1 : K) ^ ((i : ℕ) + 1) *
        (f.polynomial.map (Int.castRingHom K)).coeff
          (6 - ((i : ℕ) + 1)) =
      (elementaryValues f i : K) := by
  rw [Polynomial.coeff_map, monicSextic_polynomial_coeff_rev]
  simp [elementaryValues]

/-- The elementary symmetric functions of the chosen roots are precisely the
six signed integer coefficients supplied to the sparse formulas. -/
theorem rootTuple_esymm_eq_elementaryValues
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial) (i : Fin 6) :
    MvPolynomial.eval₂
        (Int.castRingHom f.ratPolynomial.SplittingField)
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)
        (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
      (elementaryValues f i : f.ratPolynomial.SplittingField) := by
  let p : ℚ[X] := f.ratPolynomial
  have hdeg : p.natDegree = 6 := f.ratPolynomial_natDegree
  have he := sextic_esymm_rootTuple hp f.ratPolynomial_monic hdeg
    (i + 1) (by omega)
  have hmap :
      p.map (algebraMap ℚ p.SplittingField) =
        f.polynomial.map (Int.castRingHom p.SplittingField) := by
    dsimp only [p, MonicSextic.ratPolynomial]
    rw [Polynomial.map_map]
    congr 1
  have haeval :
      MvPolynomial.aeval (rootTuple p hp hdeg)
          (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
        algebraMap ℤ p.SplittingField (elementaryValues f i) := by
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    rw [he, hmap]
    exact signed_monicSextic_coefficient f i
  rw [MvPolynomial.aeval_def] at haeval
  convert haeval using 1
  · change MvPolynomial.eval₂ (Int.castRingHom p.SplittingField)
        (rootTuple p hp hdeg) (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
      MvPolynomial.eval₂ (algebraMap ℤ p.SplittingField)
        (rootTuple p hp hdeg) (MvPolynomial.esymm (Fin 6) ℤ (i + 1))
    rw [RingHom.eq_intCast' (algebraMap ℤ p.SplittingField)]
  · change Int.castRingHom p.SplittingField (elementaryValues f i) =
      algebraMap ℤ p.SplittingField (elementaryValues f i)
    rw [RingHom.eq_intCast' (algebraMap ℤ p.SplittingField)]

noncomputable def pairComputedCoefficient
    (a : MonicSextic × (Fin 2 → ℕ) × Fin 16) : ℤ :=
  SparseEvaluation.eval (elementaryValues a.1)
    (pairElementarySparse (a.2.1, a.2.2))

noncomputable def tripleComputedCoefficient
    (a : MonicSextic × (Fin 2 → ℕ) × Fin 11) : ℤ :=
  SparseEvaluation.eval (elementaryValues a.1)
    (tripleElementarySparse (a.2.1, a.2.2))

theorem pairComputedCoefficient_computable :
    Computable pairComputedCoefficient := by
  exact SparseEvaluation.eval_primrec.to_comp.comp
    (elementaryValues_primrec.to_comp.comp Computable.fst)
    (pairElementarySparse_computable.comp
      (Computable.pair
        (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)))

theorem tripleComputedCoefficient_computable :
    Computable tripleComputedCoefficient := by
  exact SparseEvaluation.eval_primrec.to_comp.comp
    (elementaryValues_primrec.to_comp.comp Computable.fst)
    (tripleElementarySparse_computable.comp
      (Computable.pair
        (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)))

/-- Ascending coefficients `0,...,15` of the computed pair resolvent. -/
noncomputable def pairComputedCoefficients
    (a : MonicSextic × (Fin 2 → ℕ)) : List ℤ :=
  List.ofFn fun n : Fin 16 ↦ pairComputedCoefficient (a.1, a.2, n)

/-- Ascending coefficients `0,...,10` of the computed triple resolvent. -/
noncomputable def tripleComputedCoefficients
    (a : MonicSextic × (Fin 2 → ℕ)) : List ℤ :=
  List.ofFn fun n : Fin 11 ↦ tripleComputedCoefficient (a.1, a.2, n)

theorem pairComputedCoefficients_computable :
    Computable pairComputedCoefficients := by
  apply Computable.list_ofFn
  intro n
  exact pairComputedCoefficient_computable.comp
    (Computable.pair Computable.fst
      (Computable.pair Computable.snd (Computable.const n)))

theorem tripleComputedCoefficients_computable :
    Computable tripleComputedCoefficients := by
  apply Computable.list_ofFn
  intro n
  exact tripleComputedCoefficient_computable.comp
    (Computable.pair Computable.fst
      (Computable.pair Computable.snd (Computable.const n)))

/-! ## Correctness of specialization -/

theorem sparse_eval_aeval_esymm {K : Type*} [CommRing K]
    (values : Fin 6 → ℤ) (r : Fin 6 → K) (q : SparsePolynomial)
    (hesymm : ∀ i : Fin 6,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
        (values i : K)) :
    (SparseEvaluation.eval values q : K) =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
          (SparsePolynomial.toMv q)) := by
  rw [SparseEvaluation.cast_eval, MvPolynomial.aeval_def,
    ← MvPolynomial.C_eq_algebraMap,
    ← MvPolynomial.eval₂_assoc]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  exact (hesymm i).symm

theorem pairComputedCoefficient_cast_eq
    {K : Type*} [CommRing K] (f : MonicSextic)
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (n : Fin 16)
    (hesymm : ∀ i : Fin 6,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
        (elementaryValues f i : K)) :
    (pairComputedCoefficient (f, x, n) : K) =
      (pairEvaluatedResolvent x r).coeff n := by
  rw [pairComputedCoefficient,
    sparse_eval_aeval_esymm (elementaryValues f) r _ hesymm,
    pairElementarySparse_correct]
  rw [← pairUniversalEvaluatedResolvent_specialize x r,
    Polynomial.coeff_map]
  rfl

theorem tripleComputedCoefficient_cast_eq
    {K : Type*} [CommRing K] (f : MonicSextic)
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (n : Fin 11)
    (hesymm : ∀ i : Fin 6,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
        (elementaryValues f i : K)) :
    (tripleComputedCoefficient (f, x, n) : K) =
      (tripleEvaluatedResolvent x r).coeff n := by
  rw [tripleComputedCoefficient,
    sparse_eval_aeval_esymm (elementaryValues f) r _ hesymm,
    tripleElementarySparse_correct]
  rw [← tripleUniversalEvaluatedResolvent_specialize x r,
    Polynomial.coeff_map]
  rfl

theorem pairComputedCoefficient_rootTuple
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) (n : Fin 16) :
    (pairComputedCoefficient (f, x, n) :
        f.ratPolynomial.SplittingField) =
      (pairEvaluatedResolvent x
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)).coeff n := by
  apply pairComputedCoefficient_cast_eq
  exact rootTuple_esymm_eq_elementaryValues f hp

theorem tripleComputedCoefficient_rootTuple
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) (n : Fin 11) :
    (tripleComputedCoefficient (f, x, n) :
        f.ratPolynomial.SplittingField) =
      (tripleEvaluatedResolvent x
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)).coeff n := by
  apply tripleComputedCoefficient_cast_eq
  exact rootTuple_esymm_eq_elementaryValues f hp

end LeanProofs.PolynomialFormulas.SexticComputedResolvents
