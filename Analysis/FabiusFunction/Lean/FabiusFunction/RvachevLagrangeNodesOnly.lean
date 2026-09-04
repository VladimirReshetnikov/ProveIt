import FabiusFunction.CenteredMomentParity
import FabiusFunction.RvachevAppellHasse
import FabiusFunction.SinhDivBernoulliLog

/-!
# Nodes-only Rvachev--Appell amplitudes

This module closes the finite algebra in the representation manuscript's
`cor:lag-nodes-only`.  It gives both displayed forms of the deconvolved
Lagrange amplitude:

* the even ordinary-derivative sum, with the factorial normalization made
  explicit; and
* the nodal-weight sum of elementary symmetric functions times the
  Rvachev--Appell polynomials.

The second formula uses the *untranslated* nodes omitted at the selected
index, exactly as in the manuscript.  It complements the translated-node
Hasse formula in `RvachevAppellHasse` rather than replacing it.

The rationality statement is kept honest.  Rational nodes determine a
polynomial over `ℚ`, whose coefficientwise cast is the real deconvolved
Lagrange polynomial.  Consequently every rational evaluation point -- in
particular every rational lattice sample `k / M` -- has a rational amplitude.
No claim is made that evaluation at an arbitrary irrational real is rational.

Finally, the reciprocal coefficients are identified with complete Bell
polynomials in the negated full centered cumulants.  The even cumulants are
then tied to the existing all-order Bernoulli--Mersenne formula, while the odd
cumulants vanish through the existing parity theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial Set

noncomputable section

/-! ## Polynomial and derivative forms -/

/-- Rational Rvachev polynomial deconvolution.  It replaces `X ^ n` by the
rational Rvachev--Appell polynomial of the same index. -/
noncomputable def rvachevDeconvolvedPolynomialRat (P : ℚ[X]) : ℚ[X] :=
  Appell.polynomialTransform rvachevReciprocalMomentRat P

/-- Rational Rvachev deconvolution commutes with coefficientwise casting to
the reals.  This is the coefficient-level rationality statement used below. -/
theorem map_rvachevDeconvolvedPolynomialRat (P : ℚ[X]) :
    (rvachevDeconvolvedPolynomialRat P).map (Rat.castHom ℝ) =
      rvachevDeconvolvedPolynomial (P.map (Rat.castHom ℝ)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [rvachevDeconvolvedPolynomialRat] at hP hQ ⊢
      simp only [LinearMap.map_add, Polynomial.map_add,
        rvachevDeconvolvedPolynomial_add, hP, hQ]
  | monomial n a =>
      simp only [rvachevDeconvolvedPolynomialRat,
        Appell.polynomialTransform_monomial, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_monomial,
        rvachevDeconvolvedPolynomial_monomial,
        rvachevAppellPolynomialRat, rvachevAppellPolynomial]

/-- Rvachev deconvolution is the finite coefficient expansion in the
Rvachev--Appell basis. -/
theorem rvachevDeconvolvedPolynomial_eq_sum_appell (P : ℝ[X]) :
    rvachevDeconvolvedPolynomial P =
      ∑ n ∈ range (P.natDegree + 1),
        C (P.coeff n) * rvachevAppellPolynomial n := by
  unfold rvachevDeconvolvedPolynomial
  exact P.sum_over_range (fun n ↦ by simp)

private theorem eval_hasseDeriv_eq_iterateDerivative_div_factorial
    (P : ℝ[X]) (n : ℕ) (x : ℝ) :
    (hasseDeriv n P).eval x =
      ((derivative : ℝ[X] → ℝ[X])^[n] P).eval x /
        (n.factorial : ℝ) := by
  have h := congrFun
    (factorial_smul_hasseDeriv (R := ℝ) (k := n)) P
  rw [LinearMap.smul_apply, nsmul_eq_mul] at h
  have heval := congrArg (fun Q : ℝ[X] ↦ Q.eval x) h
  rw [Polynomial.eval_natCast_mul] at heval
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  apply (eq_div_iff hfac).2
  simpa only [mul_comm] using heval

/-- The even Hasse formula rewritten exactly as the manuscript's ordinary
derivatives divided by factorials. -/
theorem eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative
    (P : ℝ[X]) (x : ℝ) :
    (rvachevDeconvolvedPolynomial P).eval x =
      ∑ r ∈ range (P.natDegree / 2 + 1),
        (rvachevReciprocalMomentRat (2 * r) : ℝ) *
          (((derivative : ℝ[X] → ℝ[X])^[2 * r] P).eval x /
            ((2 * r).factorial : ℝ)) := by
  rw [rvachevDeconvolvedPolynomial_eq_sum_even_hasseDeriv,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    eval_hasseDeriv_eq_iterateDerivative_div_factorial]

/-! ## Raw-node elementary-symmetric expansion -/

/-- Deconvolution of a monic product of root factors, expressed in the
Rvachev--Appell basis using the elementary symmetric functions of the raw
roots.  Multiplicities are retained by the indexed family. -/
theorem rvachevDeconvolvedPolynomial_prod_X_sub_C_eq_sum_appell
    { ι : Type* } [Fintype ι] (a : ι → ℝ) :
    rvachevDeconvolvedPolynomial (∏ i : ι, (X - C (a i))) =
      ∑ n ∈ range (Fintype.card ι + 1),
        C ((-1 : ℝ) ^ (Fintype.card ι - n) *
            elementarySymmetricEval a (Fintype.card ι - n)) *
          rvachevAppellPolynomial n := by
  rw [rvachevDeconvolvedPolynomial_eq_sum_appell]
  have hdegree :
      (∏ i : ι, (X - C (a i))).natDegree = Fintype.card ι := by
    rw [natDegree_prod_of_monic _ _ fun i _hi ↦ monic_X_sub_C (a i)]
    simp
  rw [hdegree]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ Fintype.card ι := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hcoeff :
      (∏ i : ι, (X - C (a i))).coeff n =
        (-1 : ℝ) ^ (Fintype.card ι - n) *
          elementarySymmetricEval a (Fintype.card ι - n) := by
    have hnle' :
        n ≤ Multiset.card (Finset.univ.val.map a) := by
      rw [Multiset.card_map]
      simpa only [Finset.card_val, Finset.card_univ] using hnle
    have h := Multiset.prod_X_sub_C_coeff
      (Finset.univ.val.map a) hnle'
    rw [Multiset.card_map] at h
    simpa only [elementarySymmetricEval, Finset.prod_eq_multiset_prod,
      Multiset.map_map, Function.comp_apply, Finset.card_val,
      Finset.card_univ] using h
  rw [hcoeff]

/-- The derivative form of a deconvolved Lagrange basis polynomial.  Node
injectivity makes its degree exactly `s.card - 1`, yielding the manuscript's
cutoff `floor ((s.card - 1) / 2)`. -/
theorem eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_sum_even_iterateDerivative
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hvs : Set.InjOn v s) {i : ι} (hi : i ∈ s) (x : ℝ) :
    (rvachevDeconvolvedPolynomial (Lagrange.basis s v i)).eval x =
      ∑ r ∈ range ((s.card - 1) / 2 + 1),
        (rvachevReciprocalMomentRat (2 * r) : ℝ) *
          (((derivative : ℝ[X] → ℝ[X])^[2 * r]
              (Lagrange.basis s v i)).eval x /
            ((2 * r).factorial : ℝ)) := by
  simpa only [Lagrange.natDegree_basis hvs hi] using
    (eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative
      (Lagrange.basis s v i) x)

/-- **Nodes-only Rvachev--Appell amplitude.**  The deconvolved Lagrange
cardinal is its nodal weight times the finite sum of raw-node elementary
symmetric coefficients against the Rvachev--Appell family.  This is the exact
second displayed identity in `cor:lag-nodes-only`, at an arbitrary real
evaluation point. -/
theorem eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {i : ι} (hi : i ∈ s) (x : ℝ) :
    (rvachevDeconvolvedPolynomial (Lagrange.basis s v i)).eval x =
      Lagrange.nodalWeight s v i *
        ∑ n ∈ range s.card,
          (-1 : ℝ) ^ (s.card - 1 - n) *
            elementarySymmetricEval
              (fun j : ↥(s.erase i) ↦ v (j : ι)) (s.card - 1 - n) *
            (rvachevAppellPolynomial n).eval x := by
  rw [lagrangeBasis_eq_nodalWeight_mul_prod_X_sub_C s v hi,
    rvachevDeconvolvedPolynomial_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C,
    rvachevDeconvolvedPolynomial_prod_X_sub_C_eq_sum_appell,
    Polynomial.eval_finsetSum]
  simp only [Fintype.card_coe, Finset.card_erase_of_mem hi,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
  rw [Nat.sub_add_cancel hcard]

/-- Sampled decoder form of the nodes-only Appell expansion.  It is total in
the mesh `M`; reconstruction theorems separately impose `M ≠ 0`. -/
theorem lagrangeRvachevDecoder_eq_nodalWeight_mul_sum_appell
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {i : ι} (hi : i ∈ s) (M : ℕ) (k : ℤ) :
    lagrangeRvachevDecoder s v M k i =
      Lagrange.nodalWeight s v i *
        ∑ n ∈ range s.card,
          (-1 : ℝ) ^ (s.card - 1 - n) *
            elementarySymmetricEval
              (fun j : ↥(s.erase i) ↦ v (j : ι)) (s.card - 1 - n) *
            (rvachevAppellPolynomial n).eval
              ((k : ℝ) / (M : ℝ)) := by
  exact
    eval_rvachevDeconvolvedPolynomial_lagrangeBasis_eq_nodalWeight_mul_sum_appell
      s v hi ((k : ℝ) / (M : ℝ))

/-! ## Rational nodes and rational samples -/

/-- A rational Lagrange basis polynomial casts coefficientwise to the real
Lagrange basis at the cast nodes. -/
theorem map_lagrangeBasis_ratCast
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (v : ι → ℚ) (i : ι) :
    (Lagrange.basis s v i).map (Rat.castHom ℝ) =
      Lagrange.basis s (fun j ↦ (v j : ℝ)) i := by
  rw [Lagrange.basis, Lagrange.basis, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  norm_num [Lagrange.basisDivisor]

/-- The real deconvolved Lagrange polynomial at rational nodes is exactly the
coefficientwise cast of a polynomial over `ℚ`. -/
theorem map_rvachevDeconvolvedPolynomialRat_lagrangeBasis
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (v : ι → ℚ) (i : ι) :
    (rvachevDeconvolvedPolynomialRat (Lagrange.basis s v i)).map
        (Rat.castHom ℝ) =
      rvachevDeconvolvedPolynomial
        (Lagrange.basis s (fun j ↦ (v j : ℝ)) i) := by
  rw [map_rvachevDeconvolvedPolynomialRat, map_lagrangeBasis_ratCast]

/-- Every decoder entry formed from rational nodes and a rational lattice
point is the cast of an explicitly rational polynomial evaluation.  This is
the precise value-level meaning of "rational amplitudes" in the cardinal
synthesis setting. -/
theorem lagrangeRvachevDecoder_eq_ratCast
    { ι : Type* } [DecidableEq ι] (s : Finset ι) (v : ι → ℚ)
    (M : ℕ) (k : ℤ) (i : ι) :
    lagrangeRvachevDecoder s (fun j ↦ (v j : ℝ)) M k i =
      ((rvachevDeconvolvedPolynomialRat (Lagrange.basis s v i)).eval
          ((k : ℚ) / (M : ℚ)) : ℚ) := by
  rw [lagrangeRvachevDecoder,
    ← map_rvachevDeconvolvedPolynomialRat_lagrangeBasis]
  have hpoint :
      (((k : ℚ) / (M : ℚ) : ℚ) : ℝ) =
        (k : ℝ) / (M : ℝ) := by
    norm_num
  rw [← hpoint]
  change
    ((rvachevDeconvolvedPolynomialRat (Lagrange.basis s v i)).map
        (Rat.castHom ℝ)).eval
        (((k : ℚ) / (M : ℚ) : ℚ) : ℝ) =
      (Rat.castHom ℝ)
        ((rvachevDeconvolvedPolynomialRat (Lagrange.basis s v i)).eval
          ((k : ℚ) / (M : ℚ)))
  exact Polynomial.eval_map_apply
    (p := rvachevDeconvolvedPolynomialRat (Lagrange.basis s v i))
    (f := Rat.castHom ℝ) ((k : ℚ) / (M : ℚ))

/-! ## Complete Bell polynomials and Bernoulli cumulants -/

/-- The raw moment sequence used by the Rvachev--Appell construction is the
ordinary full centered Rvachev moment sequence. -/
theorem rvachevRawMomentRat_eq_centeredRvachevFullMoment :
    rvachevRawMomentRat = centeredRvachevFullMoment := by
  funext n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp
  · simp

/-- The formal cumulants of the Appell raw moments are exactly the full
centered Rvachev cumulants. -/
theorem momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant :
    momentCumulant rvachevRawMomentRat = centeredRvachevFullCumulant := by
  rw [rvachevRawMomentRat_eq_centeredRvachevFullMoment]
  unfold centeredRvachevFullMoment centeredRvachevFullCumulant
  exact momentCumulant_factorialDenormalize
    centeredRvachevFullMomentCoefficient

/-- Every positive even cumulant in the Rvachev--Appell raw-moment sequence
has the all-order Bernoulli--Mersenne closed form from the manuscript. -/
theorem momentCumulant_rvachevRawMomentRat_even_eq_bernoulliMersenne
    (n : ℕ) (hn : 1 ≤ n) :
    momentCumulant rvachevRawMomentRat (2 * n) =
      (2 : ℚ) ^ (2 * n - 1) * _root_.bernoulli (2 * n) /
        ((n : ℚ) * ((4 : ℚ) ^ n - 1)) := by
  calc
    momentCumulant rvachevRawMomentRat (2 * n) =
        centeredRvachevFullCumulant (2 * n) :=
      congrFun
        momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant
        (2 * n)
    _ = centeredRvachevEvenCumulant n :=
      centeredRvachevFullCumulant_even n
    _ = _ := centeredRvachevEvenCumulant_eq_bernoulliMersenne_formula n hn

/-- The reciprocal Rvachev moments are complete Bell polynomials in the
negatives of the full centered cumulants.  Together with the preceding even
Bernoulli formula and `centeredRvachevFullCumulant_odd`, this is the exact
Bernoulli--Bell coefficient claim in `cor:lag-nodes-only`. -/
theorem rvachevReciprocalMomentRat_eq_completeBellPolynomial_neg_centeredCumulant :
    rvachevReciprocalMomentRat =
      completeBellPolynomial (-centeredRvachevFullCumulant) := by
  rw [rvachevReciprocalMomentRat_eq_completeBellPolynomial,
    momentCumulant_rvachevRawMomentRat_eq_centeredRvachevFullCumulant]

end

end Fabius
