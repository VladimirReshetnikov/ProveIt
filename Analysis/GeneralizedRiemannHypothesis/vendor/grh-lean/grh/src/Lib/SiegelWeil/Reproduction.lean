import Lib.DiscreteSeries.Holomorphic.ModelFunction
import Lib.SiegelWeil.RallisInner.SharpData
import Lib.Weil.DualPair.HolomorphicData

/-!
# Holomorphic Fock vectors and a reproducing formula by theta lifts

Polynomial vectors in the Fock model of a pair of unitary groups with signs `s` and `s'`: their
coefficients, their weights and the span of their translates. Then the reproducing formula, whose
hypotheses these facts supply.

* `New.Rows.linSubst_variableMinor`, `New.Rows.polyMatrixCoeff_eq_holMinorsPi_mul_conj`: a minor of
  variables is scaled by a principal minor of the group element. For a polynomial in the variables
  of sign `1` that is scaled in this way, the coefficient at `(u, 1)` is its value at `(1, 1)` times
  a function `holMinorsPi` times the conjugate of another.
* `New.Rows.prod_variableMinor_mem_holomorphicData`,
  `New.Rows.letterPoly_highestVector_mem_holomorphicData`: two families of nonzero holomorphic
  vectors.
* `New.Rows.realPairWeil_mem_span_pairedDetProd`: the definite second group moves a power of a minor
  into the span of the products of minors of Y times the matrix of variables, for any invertible
  matrix Y over E.
* `New.Rows.reproducing_formula_modKernel`: at each point, convolution with `holMinorsPi s u` is a
  finite combination of values of theta lifts to a definite group of rank above `2 * card n`.

Notions from other files:
* `New.PairFock E s s'`: the Fock space of `n' × n` matrices at every infinite place, with the signs
  `New.homSigns s s'`, that is `s'(i) s(j)`, repeated at every place by `New.realSigns`.
* `New.Fock.polyVector`: the linear map P ↦ v_P from complex polynomials to the Fock space,
  v_P(x) = P(ζ(x))exp(−|x|²/2), where ζ(x)_i is x̄_i at positive and x_i at negative coordinates.
* `New.realPairWeil γ e`: the real Weil representation of the pair of unitary groups, twisted by
  `det ^ (-e)` on the first group and `det ^ γ` on the second.
* `New.Rows.holomorphicData s s' O u γ e`: the Fock vectors all of whose coefficients are
  holomorphic of weight `u` on the first group, for the order `O` of its coordinates.
* `New.holMinorsPi s u`: the product over the infinite places of the quotients of minors of weight
  `u`, a function on the product of the unitary groups of signs `s`.

## Relation to the literature

Known result: Basis problem in the stable range, as a reproducing formula. This is a unitary version
at a fixed level, in which pairing with a holomorphic discrete series coefficient is, at each point,
a finite combination, the same for all functions of that level, of values of theta lifts to a large
definite group. It is deduced from injectivity by linear duality. Source: S. Böcherer, Über die
Fourier-Jacobi-Entwicklung Siegelscher Eisensteinreihen, Math. Z. 183 (1983); J.-S. Li, Crelle 428
(1992).

See also `Lib.Weil.Fock.OscillatorPair` and `Lib.Weil.DualPair.HolomorphicData`.
-/

namespace New.Rows

open MeasureTheory Set Matrix Fock SiegelWeil MvPolynomial Finset Submodule NumberField Sum
  Heisenberg.IsVacuum Fintype ComplexConjugate Space Function Exchange Complex

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable {s : n → ℤˣ} {O : n → ℤ} {E : Type} [Field E] [CMType E]
variable {p q : Type} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] {s' : n' → ℤˣ}

/-! ### The coefficient of a product of minors -/

/-- Let the rows `i a` all have sign `κ` for `s'` and let `c` enumerate the indices of sign `κ`
for `s`. The linear substitution of the matrix variables `X (τ, r, k)` by which `(u⁻¹, 1)` acts
multiplies `variableMinor τ i c`, the minor of the variables at the place `τ` in rows `i` and
columns `c`, by the principal minor of `u τ` on the indices of sign `κ`. -/
lemma linSubst_variableMinor {i : p → n'} {c : p → n} {κ : ℤˣ} (hi : ∀ a : p, s' (i a) = κ)
    (hc : c.Injective) (h_range : ∀ k : n, s k = κ ↔ k ∈ Set.range c) (u : GInf E s)
    (τ : InfinitePlace E) :
    linSubst (complexLinearPart (pairHomInf (s' := s') (u⁻¹, 1))) (variableMinor τ i c) =
      principalMinor (u τ) (fun k : n ↦ s k = κ) • variableMinor τ i c := by
  -- The substitution multiplies the transposed matrix of variables on the left by the block of
  -- `u τ` on the indices of sign `κ`, which `c` enumerates; take determinants.
  have h_var (a b : p) :
      linSubst (complexLinearPart (pairHomInf (s' := s') (u⁻¹, 1))) (X (τ, i b, c a)) =
        ∑ j : p, (u τ : Matrix n n ℂ) (c a) (c j) • X (τ, i b, c j) := calc
    _ = ∑ k : n, (if s k = κ then (u τ : Matrix n n ℂ) (c a) k else 0) • X (τ, i b, k) := by
      simp [complexLinearPart, linSubst, posProj, blockDiagonal_apply, (h_range _).2, hi,
        sum_prod_type, mul_eq_one_iff_eq_inv', one_apply, pairSign, pairHomInf, pairHom]
    _ = _ := (sum_of_injective c hc _ _ (by simp +contextual [h_range]) (by simp [h_range])).symm
  have h_minor : principalMinor (u τ) (fun k : n ↦ s k = κ) =
      (of fun a b : p ↦ (u τ : Matrix n n ℂ) (c a) (c b)).det :=
    (det_submatrix_equiv_self
      ((Equiv.ofInjective c hc).trans (Equiv.subtypeEquivRight h_range).symm) _).symm
  rw [variableMinor, ← det_transpose, AlgHom.map_det, ← C_mul', h_minor, C.map_det, ← det_mul]
  exact congrArg det (Matrix.ext fun a b ↦ by simpa [mul_apply, C_mul'] using h_var a b)

/-- The principal minor of the action of `(u, 1)` on matrices of variables, on the variables of sign
`-1` for `homSigns s s'`, is the product over the places `w` and the rows `r` of the minor of `u w`
of sign `s' r` over `det (u w)`. -/
lemma principalMinor_pairHomInf_neg (s : n → ℤˣ) (s' : n' → ℤˣ) (u : GInf E s) :
    principalMinor (pairHomInf (s' := s') (u, 1))
        (fun i : InfinitePlace E × n' × n ↦ realSigns E (homSigns s s') i = -1) =
      ∏ w : InfinitePlace E,
        (principalMinor (u w) (fun k : n ↦ s k = 1) / (u w : Matrix n n ℂ).det) ^
          card {r : n' // s' r = 1} *
        (principalMinor (u w) (fun k : n ↦ s k = -1) / (u w : Matrix n n ℂ).det) ^
          card {r : n' // s' r = -1} := by
  -- The minor splits over the places and the rows; the row `r` gives the minor of `(u w)⁻¹` of
  -- sign `-s' r`, which `jacobi_complementary_minor` turns into that of `u w` of sign `s' r`.
  have by_sign (w : InfinitePlace E) :
      ∏ σ : ℤˣ, ∏ _r : {r : n' // s' r = σ},
          principalMinor (u w) (fun k : n ↦ σ * s k = 1) / (u w : Matrix n n ℂ).det =
        ∏ r : n', principalMinor (u w) (fun k : n ↦ s' r * s k = 1) / (u w : Matrix n n ℂ).det :=
    prod_fiberwise' s' _
  simp [one_kronecker, jacobi_complementary_minor, neg_eq_iff_eq_neg, div_pow, div_mul_div_comm,
    ← by_sign, pairHomInf, pairHom, pairSign, Int.units_ne_iff_eq_neg,
    GeneralLinearGroup.det_ne_zero]

/-- Let `P` be a polynomial in the variables of sign `1` for `homSigns s s'`, those `(w, r, k)` with
`s' r * s k = 1`, that the substitution attached to `u⁻¹` multiplies by the powers `ν`, `c` of the
two principal minors of `u`. Its coefficient `polyMatrixCoeff` (the pairing of its Fock vector with
the translate by `(u, 1)`) is the value at `(1, 1)` times `holMinorsPi s v u` times the conjugate of
`holMinorsPi s k u`, for `v = (-ν; r₊) + r₋ - e` and `k = (0; c + r₋)`. Here `r₋ = negCount s'`
and `r₊ = card n' - r₋` count the signs of `s'`, `(a; b)` has entries `a` where `s = 1` and `b`
elsewhere, and `e` is the weight of the character on the first group (`e = r₋` for the standard
splitting). -/
lemma polyMatrixCoeff_eq_holMinorsPi_mul_conj (s : n → ℤˣ) (s' : n' → ℤˣ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (hP : P ∈ supported ℂ {p : InfinitePlace E × n' × n | realSigns E (homSigns s s') p = 1})
    {ν c : InfinitePlace E → ℕ} (γ e : InfinitePlace E → ℤ)
    (hscale : ∀ u : GInf E s, linSubst (complexLinearPart (pairHomInf (s' := s') (u⁻¹, 1))) P =
      (∏ w : InfinitePlace E, principalMinor (u w) (fun k : n ↦ s k = 1) ^ ν w *
        principalMinor (u w) (fun k : n ↦ s k = -1) ^ c w) • P)
    (u : GInf E s) :
    polyMatrixCoeff s s' γ e P u 1 = polyMatrixCoeff s s' γ e P 1 1 *
      holMinorsPi s (fun (w : InfinitePlace E) (i : n) ↦
        if s i = 1 then -ν w + (negCount s' - e w)
        else (card n' - negCount s' : ℕ) + (negCount s' - e w)) u *
      conj (holMinorsPi s (fun (w : InfinitePlace E) (i : n) ↦
        if s i = 1 then 0 else c w + negCount s') u) := by
  -- `P` has no variable of sign `-1`, so it is harmonic, even with all coordinates in one group,
  -- and `fockMatrixCoeff_eq_fockInner` applies: the coefficient is `⟨v_P', v_P⟩` over the
  -- negative minor of `pairHomInf (u, 1)` and over `∏ det (u w) ^ e w`, with `P'` the substitution
  -- of `P` by `(complexLinearPart (pairHomInf (u, 1)))⁻¹`, which only scales `P`.
  let σ : InfinitePlace E × n' × n → ℤˣ := realSigns E (homSigns s s')
  have harmonic (i j : InfinitePlace E × n' × n) (h : σ i ≠ σ j) : pderiv i (pderiv j P) = 0 := by
    have h_neg {k : InfinitePlace E × n' × n} (hk : σ k ≠ 1) : pderiv k P = 0 :=
      pderiv_eq_zero_of_notMem_vars fun hk' ↦ hk (mem_supported.1 hP hk')
    by_cases hj : σ j = 1
    · rw [New.pderiv_comm, h_neg (h.trans_eq hj), map_zero]
    · rw [h_neg hj, map_zero]
  let t : ℂ := ∏ w : InfinitePlace E, principalMinor (u⁻¹ w) (fun k : n ↦ s k = 1) ^ ν w *
    principalMinor (u⁻¹ w) (fun k : n ↦ s k = -1) ^ c w
  have scale : linSubst (complexLinearPart (pairHomInf (s' := s') (u, 1)))⁻¹ P = t⁻¹ • P := by
    have ht : t ≠ 0 := by simp [t, prod_ne_zero_iff, U.principalMinor_sign_ne_zero, -Pi.inv_apply]
    rw [eq_inv_smul_iff₀ ht, ← map_smul, ← hscale u⁻¹, ← linSubst_mul]
    simp
  have coeff : polyMatrixCoeff s s' γ e P u 1 =
      (∏ w : InfinitePlace E, (u w : Matrix n n ℂ).det ^ e w)⁻¹ *
        (principalMinor (pairHomInf (s' := s') (u, 1)) fun i ↦ σ i = -1)⁻¹ *
        conj t⁻¹ * polyMatrixCoeff s s' γ e P 1 1 := by
    rw [polyMatrixCoeff, polyMatrixCoeff, realPairWeil_apply_apply, map_smul, ← fockMatrixCoeff,
      fockMatrixCoeff_eq_fockInner _ (d := const _ ()) (by simp)
      _ (fun i j _ ↦ harmonic i j) _ (fun i j _ ↦ harmonic i j), scale]
    simp [σ, mul_assoc, Prod.mk_one_one]
  -- The negative minor splits over the places and the rows, and the weights are constant on each
  -- sign, so both sides are products of powers of `det (u w)` and of its two minors, all nonzero.
  rw [coeff, principalMinor_pairHomInf_neg]
  simp (disch := lia) only [holMinorsPi, holMinors_ite_sign]
  simp [t, negCount, ← card_subtype_compl, ← U.principalMinor_coe_inv, ← inv_eq_conj,
    jacobi_complementary_minor, zpow_add₀, zpow_sub₀, div_pow, prod_mul_distrib,
    Int.units_ne_iff_eq_neg, GeneralLinearGroup.det_ne_zero]
  field_simp [prod_ne_zero_iff, GeneralLinearGroup.det_ne_zero]

/-! ### Holomorphic products of minors and their translates -/

/-- For signs `+1` on `p` and `-1` on `q`, an order `O` that puts `p` first and a definite second
space of coordinates `n'`, let `Q` be the product over the infinite places of the `d`-th power of
the minor (`variableMinor`) in rows `i` and all the positive columns. Then `Q ≠ 0` and its Fock
vector is holomorphic (`holomorphicData`) of weight `-d` on `p` and `card n'` on `q`, for the
character weights `γ` and `0`. -/
lemma prod_variableMinor_mem_holomorphicData {O : p ⊕ q → ℤ}
    (ho : IsPosFirstOrder (n := p ⊕ q) (1 ⊕ᵥ -1) O) (i : p ↪ n') (d : ℕ) (γ : InfinitePlace E → ℤ) :
    let Q : MvPolynomial (InfinitePlace E × n' × (p ⊕ q)) ℂ :=
      ∏ w : InfinitePlace E, ∏ _ : Fin d, variableMinor w i inl
    Q ≠ 0 ∧
    polyVector (realSigns E (homSigns (1 ⊕ᵥ -1) 1)) Q ∈ holomorphicData (E := E) (1 ⊕ᵥ -1) 1 O
      (fun _ : InfinitePlace E ↦ -d ⊕ᵥ Fintype.card n') γ 0 := by
  -- At each place the polynomial is the product of `d` equal layers, the minor on the rows `i` and
  -- the positive columns; `IsLayering.isJointHighest_of_eq_prod_det` makes it a joint harmonic and
  -- `prod_mem_holomorphicData` concludes.
  let ρ : Fin d → p → n' := fun _ ↦ i
  let κ : Fin d → p → p ⊕ q := fun _ ↦ inl
  let T (w : InfinitePlace E) : FockDualPair (1 : n' → ℤˣ) (1 ⊕ᵥ -1 : p ⊕ q → ℤˣ) (n' × (p ⊕ q)) :=
    FockDualPair.std 1 (1 ⊕ᵥ -1) (γ w) (-0) -- `-0`, as in `prod_mem_holomorphicData`
  let ν (w : InfinitePlace E) (r : n') : ℤ :=
    (T w).vacuumWeight 1 + ∑ t : Fin d, ∑ a : p with ρ t a = r, ((T w).varSign (r, κ t a)).1
  have h_rows (w : InfinitePlace E) : IsLayering (T w) 0 (ν w) ρ κ :=
    { injective _ := i.2, sign_eq := by simp [κ], closed := by simp, weight_eq _ := rfl }
  have h_cols (w : InfinitePlace E) : IsLayering (T w).swap (-O) (-d ⊕ᵥ card n') κ ρ :=
    { injective _ := inl_injective, sign_eq := by simp, closed := by simp [κ, T]
      weight_eq := by simp [κ, T, filter_eq', vacuumWeight, pairSign] }
  exact prod_mem_holomorphicData ho (l := fun _ ↦ O) (by simp)
    (fun w ↦ (h_rows w).isJointHighest_of_eq_prod_det (h_cols w) rfl)
    (by simp [ρ, κ, T, variableMinor, AlgHom.map_det, Matrix.map])

/-- For signs `+1` on `p` and `-1` on `q`, let `Y` be an invertible matrix over `E`. An element `y`
of the definite second group maps, under `realPairWeil`, the Fock vector of the product over the
places `w` of the `d`-th power of the minor in rows `i` and the columns of sign `+1` into the span
of the Fock vectors of `pairedDetProd`: for a choice `I` of rows, the product over `w` and `k` of
the determinants of the rows `I w k` of `Φ w Y` times the positive columns of variables, `Φ w`
being the chosen embedding of `E` at `w`. -/
lemma realPairWeil_mem_span_pairedDetProd (i : p → n') {Y : Matrix n' n' E} (hY : IsUnit Y) (d : ℕ)
    (γ : InfinitePlace E → ℤ) (y : GInf E 1) :
    realPairWeil (s := 1 ⊕ᵥ -1) (s' := 1) γ 0 (1, y)
        (polyVector (realSigns E (homSigns (1 ⊕ᵥ -1) 1))
          (∏ w : InfinitePlace E, ∏ _ : Fin d, variableMinor w i (inl : p → p ⊕ q))) ∈
      span ℂ (Set.range fun I : InfinitePlace E → Fin d → p → n' ↦
        polyVector (realSigns E (homSigns (1 ⊕ᵥ -1) 1))
          (pairedDetProd (fun (w : InfinitePlace E) (k : n') (b : p) ↦ X (w, k, inl b))
            fun (w : InfinitePlace E) (k : Fin d) ↦ (Y.map (Φ w)).submatrix (I w k) id)) := by
  -- `(1, y)` substitutes `yᵀ` in the positive columns. As `Y` is invertible, the rows of `yᵀ` are
  -- combinations of the rows of `Y`, and multilinearity of the determinant expands each
  -- substituted minor as a combination of minors in the rows of `Y`.
  have h_rows (w : InfinitePlace E) (a : n') :
      ∃ v : n' → ℂ, ∀ k : n', ∑ c : n', v c * Φ w (Y c k) = (y w : Matrix n' n' ℂ) k a := by
    obtain ⟨v, hv⟩ := vecMul_surjective_iff_isUnit.2 (hY.map (Φ w).mapMatrix)
      ((y w : Matrix n' n' ℂ)ᵀ a)
    exact ⟨v, congrFun hv⟩
  choose M hM using h_rows
  -- `row w c` is the row `c` of `Φ w Y` times the positive columns of variables at `w`
  let row (w : InfinitePlace E) (c : n') (b : p) :
      MvPolynomial (InfinitePlace E × n' × (p ⊕ q)) ℂ := ∑ k, C (Φ w (Y c k)) * X (w, k, inl b)
  -- By `realPairWeil_polyVector`, `(1, y)` acts as a scalar times a linear substitution `σ` of the
  -- variables; only the effect of `σ` on the positive columns matters.
  rw [realPairWeil_polyVector _ _ (by simp) (by simp)]
  refine smul_mem _ _ ?_
  generalize hσ : (aeval _ : MvPolynomial _ ℂ →ₐ[ℂ] MvPolynomial _ ℂ) = σ
  have h_entry (w : InfinitePlace E) (a : n') (b : p) :
      σ (X (w, a, inl b)) = (∑ c : n', M w a c • row w c) b := by
    simpa [← hσ, row, ← hM, sum_smul, mul_smul, C_mul', smul_sum, Matrix.one_apply] using sum_comm
  have h_minor (w : InfinitePlace E) : σ (variableMinor w i inl) =
      ∑ r : p → n', (∏ a : p, M w (i a) (r a)) • (of fun a ↦ row w (r a)).det := calc
    _ = (of fun a : p ↦ ∑ c : n', M w (i a) c • row w c).det :=
      (σ.map_det _).trans (congrArg det (Matrix.ext fun a b ↦ h_entry w (i a) b))
    -- the determinant is multilinear in its rows
    _ = ∑ r : p → n', (of fun a : p ↦ M w (i a) (r a) • row w (r a)).det :=
      detRowAlternating.toMultilinearMap.map_sum fun a c ↦ M w (i a) c • row w c
    _ = _ := Finset.sum_congr rfl fun r _ ↦
      (detRowAlternating.toMultilinearMap.restrictScalars ℂ).map_smul_univ _ fun a ↦ row w (r a)
  simp only [map_prod σ, h_minor, prod_univ_sum, prod_smul, map_sum, map_smul]
  -- by definition `pairedDetProd` is a product of minors in the rows `row w c`
  exact sum_smul_mem _ _ fun r _ ↦ subset_span ⟨r, rfl⟩

/-- Let the order `O` put the sign `+1` first. (a) Within each sign the parameter `l` increases
along `O`, and `l` is injective. (b) `o a` counts the indices `b` of the sign of `a`
with `s a * l a < s a * l b`. (c) The column multiplicities `κ τ i` vanish for `i` above the
number of indices of sign `c`. Let `Q` be the polynomial `letterPoly` of the highest vector of
weight `κ`: the product over the places `τ` and the sizes `i < card n'` of the `κ τ i`-th powers
of minors of size `i` of the variables, on the rows where `equivFin n'` takes its `i` largest
values and the columns `a` of sign `c` with `o a < i`. Then `Q` is nonzero and its Fock vector is
holomorphic (`holomorphicData`), for the character weights `γ` and `w`, of weight `staircaseWeight`:
at each column the vacuum weight shifted by `-w τ`, minus the sign times the number of these minors
that contain the column. -/
lemma letterPoly_highestVector_mem_holomorphicData (hO : IsPosFirstOrder s O) {E : Type} [Field E]
    [CMType E] {o : n → ℕ} {l : n → ℤ}
    (hl : ∀ a b : n, s a = s b → O a < O b → l a < l b) (hl_inj : l.Injective)
    (ho_count : ∀ a : n, o a = #{b : n | s b = s a ∧ s a * l a < s a * l b}) (c : ℤˣ)
    {κ : InfinitePlace E → ℕ → ℕ} {γ w : InfinitePlace E → ℤ}
    (hκ : ∀ (τ : InfinitePlace E) (i : ℕ), Fintype.card {a : n // s a = c} < i → κ τ i = 0) :
    let Q : MvPolynomial (InfinitePlace E × n' × n) ℂ :=
      letterPoly s o c κ (highestVector κ fun (_ : InfinitePlace E) (i : n') ↦ equivFin n' i)
    Q ≠ 0 ∧
    polyVector (realSigns E (homSigns s 1)) Q ∈ holomorphicData (E := E) s 1 O
      (fun τ : InfinitePlace E ↦ staircaseWeight n' s o (Pi.single c (κ τ)) (-w τ)) γ w := by
  -- At each place the polynomial is the staircase of `isJointHighest_prod_det_pow_staircaseWeight`
  -- with minors of sign `c` only.
  have h_inj : Injective fun i : n' ↦ (c * equivFin n' i : ℤ) := by
    fin_cases c <;> simp [Fin.val_inj, Injective]
  have h_cols (τ : InfinitePlace E) (η : ℤˣ) (i : ℕ) (hi_gt : card {a : n // s a = η} < i)
      (_ : i < card n') : (Pi.single c (κ τ) : ℤˣ → ℕ → ℕ) η i = 0 := by
    obtain rfl | hη := eq_or_ne η c
    · rw [Pi.single_eq_same, hκ τ i hi_gt]
    · rw [Pi.single_eq_of_ne hη, Pi.zero_apply]
  refine prod_mem_holomorphicData hO (fun _ ↦ hl)
    (fun τ ↦ isJointHighest_prod_det_pow_staircaseWeight hl_inj h_inj ho_count (Pi.single c (κ τ))
      (h_cols τ)
      (by fin_cases c <;> simp) fun _ ↦ rfl) ?_
  -- Unfold the highest vector: it is the product of these minors.
  fin_cases c <;>
    simp [letterPoly, highestVector, weylKernel, highestPoly, tableauPoly, minor, permArray,
      fockLetters, ite_and, sum_filter, rowSubst, apply_ite, decreasingPosition, AlgHom.map_det,
      Matrix.map, staircaseBlock]

/-! ### The reproducing formula -/

/-- Let `S` have signs `s` and let the order `O` put the sign `+1` first. Let `u` be `K`-dominant
for `O`, with `holMinorsPi s u` integrable; this is the function on the real points `h` given by the
product over the infinite places `τ` of the quotients of minors of weight `u τ` at `h τ`. Let
`Q₀ ≠ 0` have a holomorphic Fock vector of weight `u` for the character weights `γ'`, `γ`. Let `c`
and `b` be the characters of the theta kernel of `S` and the standard definite space of rank
`card n'`, with `b` of weight `γ` and trivial tame part (`b.HasWeight γ 1`). Let `𝔪 = (N)` have a
prime divisor and let `card n'` exceed twice `card n`. If `ψ` is rapidly decreasing of level `N` and
its lift by the datum (`modDatum`) of `Q₀` and of the indicator of the matrix of `e : n ↪ n'` modulo
`𝔪` vanishes, then `realConv (holMinorsPi s u) ψ`, the convolution of `ψ` with it over the real
points, vanishes. -/
lemma realConv_holMinorsPi_eq_zero_of_lift_eq_zero (ho : IsPosFirstOrder s O) {E : Type} [Field E]
    [CMType E] [WeilData E] {𝔪 : Modulus E} {N : 𝓞 E} [Fact (N ≠ 0)]
    (hN : 𝔪.ideal = Ideal.span {N}) (h𝔪 : Nonempty 𝔪.places) (S : Space E n s) {c b : AutChar E}
    {γ' γ : InfinitePlace E → ℤ} {u : InfinitePlace E → n → ℤ} (hb : b.HasWeight γ 1)
    (h_dom : ∀ w : InfinitePlace E, IsKDominant s O (u w)) (h_int : Integrable (holMinorsPi s u))
    (h_rank : 2 * Fintype.card n < Fintype.card n') (e : n ↪ n')
    {Q₀ : MvPolynomial (InfinitePlace E × n' × n) ℂ} (hQ₀_ne : Q₀ ≠ 0)
    (hQ₀_hol : polyVector (realSigns E (homSigns s 1)) Q₀ ∈ holomorphicData s 1 O u γ' γ)
    {ψ : G E s → ℂ} (hψ : ψ ∈ rapidOfLevel S N) (h_lift : lift (pairThetaKer S (stdSpace E n') c b)
      (modDatum S (stdSpace E n') 𝔪 (Pi.single (inclMatrix 𝔪.ResidueRing e) 1)
        (polyVector (realSigns E (homSigns s 1)) Q₀)) ψ = 0) :
    realConv (holMinorsPi s u) ψ = 0 := by
  -- The matrix coefficient `φ` of `v₀` is holomorphic and hermitian, so it is a multiple of
  -- `holMinorsPi s u`; the vanishing of the lift kills the convolution of `ψ` with `φ`.
  let v₀ : PairFock E s (1 : n' → ℤˣ) := polyVector _ Q₀
  let Ψ : Matrix n' n 𝔪.ResidueRing → ℂ := Pi.single (inclMatrix 𝔪.ResidueRing e) 1
  let φ (h : GInf E s) : ℂ := fockInner v₀ (realPairWeil γ' γ (h, 1) v₀)
  have hermitian (h : GInf E s) : φ h⁻¹ = conj (φ h) := by
    rw [conj_modelInner, ← modelInner_weilRep (realAction _) (pairHomInf (h⁻¹, 1))]
    simp [φ, realPairWeil, rep_apply_apply, ← map_mul, inv_eq_conj, Prod.mk_one_one]
  have coeff (h : GInf E s) : φ h = holMinorsPi s u h * fockInner v₀ v₀ := by
    simpa [Prod.mk_one_one] using (hQ₀_hol (fockInner v₀)).eq_holMinorsPi_mul ho h_dom hermitian h
  -- The finite datum of `Ψ` is sharp for the level `1 mod 𝔪`, under which `ψ` is invariant.
  have sharp : IsSharp b 𝔪.places.conjClosure (vacuumDatum S (stdSpace E n') 𝔪 Ψ).1
      (𝔪.levelOfSubgroup ⊥) (star Ψ ⬝ᵥ Ψ / card (n' × n → 𝔪.ResidueRing) / card
        (GL n 𝔪.ResidueRing)) :=
    isSharp_vacuumDatum_of_mul_eq_one _ b (.inr h𝔪) (inclMatrix 𝔪.ResidueRing e)ᵀ
      (by simp [Ψ, Pi.single_apply]) (by simp) (by simp [Ψ])
  obtain ⟨h_rapid, h_inv⟩ := Submodule.mem_inf.1 hψ
  have level : HasLevel ψ (𝔪.levelOfSubgroup ⊥) :=
    forall_mem_image.2 fun k hk ↦ congrFun (h_inv ⟨k, (𝔪.mem_principalLevel_iff hN k).2 hk⟩)
  have conv_zero : realConv φ ψ = 0 :=
    realConv_eq_zero_of_lift_eq_zero sharp v₀ level h_rapid h_rank h_lift γ'
      (show Integrable φ by simp [funext coeff, h_int.mul_const])
  have h_scale : realConv φ ψ = fockInner v₀ v₀ • realConv (holMinorsPi s u) ψ := funext fun y ↦ by
    simp [realConv, coeff, ← integral_const_mul, mul_assoc, mul_left_comm (holMinorsPi s u _)]
  have inner_ne : fockInner v₀ v₀ ≠ 0 := eq_zero_of_modelInner_self.mt (by simp [v₀, hQ₀_ne])
  exact (smul_eq_zero_iff_right inner_ne).1 (h_scale.symm.trans conv_zero)

/-- Let the characters `c` and `b` define the theta kernel of a hermitian space `S` of signs `s` and
the standard definite space of rank `card n'`, let `c` have weight `γ'` and trivial tame part
(`c.HasWeight γ' 1`), let `𝔪 = (N)`, and let `ψ` be a rapidly decreasing automorphic function for
`S` (`ψ ∈ S.rapidFunctions`). For each class `p` of level `N` of the definite unitary group, let the
span of the Fock vectors of the `Q p i` contain the translates of the vector of `Q₀` by the real
points of that group. If, at each class `p`, the theta lift of `ψ` by each `Q p i`, taken with the
indicator of the matrix of the inclusion `e` modulo `𝔪` (the datum `modDatum`: the Fock vector
paired by `integrated` with the Schrödinger operator of that indicator on the vacuum), vanishes,
then the lift by `Q₀` vanishes everywhere. -/
lemma lift_modDatum_eq_zero_of_mem_span {E : Type} [Field E] [CMType E] [WeilData E]
    {𝔪 : Modulus E} {N : 𝓞 E} [Fact (N ≠ 0)] (hN : 𝔪.ideal = Ideal.span {N}) (S : Space E n s)
    {c b : AutChar E} {γ' : InfinitePlace E → ℤ} (hc : c.HasWeight γ' 1) (e : n ↪ n')
    {Q₀ : MvPolynomial (InfinitePlace E × n' × n) ℂ} {ι : Type*}
    (Q : StdClasses (principalLevel n' N) → ι → MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (h_span : ∀ (p : StdClasses (principalLevel n' N)) (y : GInf E 1),
      realPairWeil (s := s) (s' := 1) γ' 0 (1, y) (polyVector (realSigns E (homSigns s 1)) Q₀) ∈
        span ℂ (Set.range fun i : ι ↦ polyVector (realSigns E (homSigns s 1)) (Q p i)))
    {ψ : G E s → ℂ} (h_rapid : ψ ∈ S.rapidFunctions)
    (h_zero : ∀ (p : StdClasses (principalLevel n' N)) (i : ι),
      lift (pairThetaKer S (stdSpace E n') c b)
        (modDatum S (stdSpace E n') 𝔪 (Pi.single (inclMatrix 𝔪.ResidueRing e) 1)
          (polyVector (realSigns E (homSigns s 1)) (Q p i))) ψ (1, p.out) = 0) :
    lift (pairThetaKer S (stdSpace E n') c b)
      (modDatum S (stdSpace E n') 𝔪 (Pi.single (inclMatrix 𝔪.ResidueRing e) 1)
        (polyVector (realSigns E (homSigns s 1)) Q₀)) ψ = 0 := by
  -- Move `y` to the representative of its class `p` by a rational point, a point of level `N` and
  -- a real point, and expand the translate of the vector of `Q₀` in the `Q p i`.
  let T : Space E n' 1 := stdSpace E n'
  let K : ThetaKernel (𝒮 (S.hom T)) S T := pairThetaKer S T c b
  let Ψ : Matrix n' n 𝔪.ResidueRing → ℂ := Pi.single (inclMatrix 𝔪.ResidueRing e) 1
  ext y
  obtain ⟨p, g, w, hy⟩ :=
    exists_eq_map_mul_rep_mul T.embFin (principalLevel n' N) (fun p ↦ p.out_eq) y.2
  have y_eq : y = T.ratEmbed g * (1, p.out) * (1, w.1) * ((T.ratEmbed g⁻¹ * y).1, 1) :=
    Prod.ext (by simp) (hy.trans (mul_one _).symm)
  have fixed (v : PairFock E s (1 : n' → ℤˣ)) :
      pairWeil S T c b (1, 1, w.1) (modDatum S T 𝔪 Ψ v) = modDatum S T 𝔪 Ψ v := by
    simpa [hc.apply_det_eq_one w.2.1, (𝔪.mem_principalLevel_iff hN _).1, Prod.mk_one_one] using
      pairWeil_modDatum_stdLevel S T c b 𝔪 1 ⟨w, w.2.1⟩ Ψ v
  -- `Λ` sends `v` to the lift of `ψ` by the datum of `v` and `Ψ` at the class `p`.
  let Λ : PairFock E s (1 : n' → ℤˣ) →ₗ[ℂ] ℂ :=
    .proj (1, p.out) ∘ₗ K.liftBilin.flip ⟨ψ, h_rapid⟩ ∘ₗ ((integrated (S.hom T)).flip
      ((S.hom T).schrodingerOp 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix)) (S.hom T).vacElem)).1
  have hΛ (v : PairFock E s (1 : n' → ℤˣ)) : Λ v = lift K (modDatum S T 𝔪 Ψ v) ψ (1, p.out) := rfl
  have moved (v : PairFock E s (1 : n' → ℤˣ)) : lift K (modDatum S T 𝔪 Ψ v) ψ y =
      Λ (realPairWeil (s := s) (s' := 1) γ' 0 (1, (T.ratEmbed g⁻¹ * y).1) v) := by
    simp only [hΛ, modDatum] at fixed ⊢
    conv_lhs => rw [y_eq]
    rw [lift_mul_right, lift_mul_right, K.fixesLeft_lift _ ⟨g, rfl⟩,
      pairWeil_integrated_right c, fixed]
  -- `Λ` vanishes on the span of the `Q p i`.
  exact (moved _).trans (mem_span.1 (h_span p _) Λ.ker (range_subset_iff.2 (h_zero p)))

/-- Reproducing formula. Let the order `O` put the sign `+1` first, and let `S` be a hermitian space
over `E` of signs `s`. Assume: (a) `𝔪 = (N)` has a prime divisor, and the characters `c` and `b`
have weights `γ'` and `γ` and trivial tame part; (b) `u` is `K`-dominant for `O` and
`holMinorsPi s u` (the product over infinite places `w` of the quotients of minors `holMinors` of
weight `u w`) is integrable; (c) the definite space `New.stdSpace` of rank `card n'` has more than
twice the rank of `S`; (d) `Q₀ ≠ 0` and its Fock vector is holomorphic of weight `u` for the
character weights `γ'` and `γ`; (e) for each class `p` of level `N` of the unitary group of this
definite space, the span of the Fock vectors of the `Q p i` contains the translates of that of `Q₀`
by the real points of that group. Then for each point `x` there are constants `a` such that, for all
`ψ` in `rapidOfLevel S N` (rapidly decreasing, automorphic and of level `N`), the integral
`∫ ψ(x (h, 1)) holMinorsPi s u h dh` over `h` in the archimedean group `∏_w U(diag s)` is the sum of
`a (p, i)` times the integral of `ψ` against the theta kernel `modKernelStdSpace` at the class `p`
(the kernel of the lift by `pairThetaKer S (stdSpace E n') c b` with the datum `modDatum`), taken
with polynomial `Q p i` and, modulo `𝔪`, the indicator of the matrix of the inclusion `e`. -/
lemma reproducing_formula_modKernel (ho : IsPosFirstOrder s O) {E : Type} [Field E] [CMType E]
    [WeilData E] {𝔪 : Modulus E} {N : 𝓞 E} [Fact (N ≠ 0)]
    (hN : 𝔪.ideal = Ideal.span {N}) (h𝔪 : Nonempty 𝔪.places) (S : Space E n s) {c b : AutChar E}
    {γ' γ : InfinitePlace E → ℤ} {u : InfinitePlace E → n → ℤ} (hc : c.HasWeight γ' 1)
    (hb : b.HasWeight γ 1) (h_dom : ∀ w : InfinitePlace E, IsKDominant s O (u w))
    (h_int : Integrable (holMinorsPi s u)) (h_rank : 2 * Fintype.card n < Fintype.card n')
    (e : n ↪ n') {Q₀ : MvPolynomial (InfinitePlace E × n' × n) ℂ} (hQ₀_ne : Q₀ ≠ 0)
    (hQ₀_hol : polyVector (realSigns E (homSigns s 1)) Q₀ ∈ holomorphicData s 1 O u γ' γ)
    {ι : Type*} [Fintype ι]
    (Q : StdClasses (principalLevel n' N) → ι → MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (h_span : ∀ (p : StdClasses (principalLevel n' N)) (y : GInf E 1),
      realPairWeil (s := s) (s' := 1) γ' 0 (1, y) (polyVector (realSigns E (homSigns s 1)) Q₀) ∈
        span ℂ (Set.range fun i : ι ↦ polyVector (realSigns E (homSigns s 1)) (Q p i)))
    (x : (InfinitePlace E → USign s) × Gf E n) :
    ∃ a : StdClasses (principalLevel n' N) × ι → ℂ, ∀ ψ : G E s → ℂ, ψ ∈ rapidOfLevel S N →
      ∫ h : InfinitePlace E → USign s, ψ (x * (h, 1)) * holMinorsPi s u h =
        ∑ i : StdClasses (principalLevel n' N) × ι,
          a i * ∫ g : G E s, ψ g * modKernelStdSpace S c b 𝔪
            (Pi.single (inclMatrix 𝔪.ResidueRing e) 1)
            (Q i.1 i.2) g i.1.out ∂S.quotMeasure := by
  -- On the space `rapidOfLevel S N` the left side is a linear form `ℓ` and the pairings on the
  -- right are linear forms `L i`. It is enough that `ℓ` vanishes where all `L i` do. There the
  -- theta lift by `Q₀` is `0`, so the convolution with `holMinorsPi s u` vanishes.
  let T : Space E n' 1 := stdSpace E n'
  let K : ThetaKernel (𝒮 (S.hom T)) S T := pairThetaKer S T c b
  let Ψ : Matrix n' n 𝔪.ResidueRing → ℂ := Pi.single (inclMatrix 𝔪.ResidueRing e) 1
  let L (i : StdClasses (principalLevel n' N) × ι) : rapidOfLevel S N →ₗ[ℂ] ℂ :=
    .proj (1, i.1.out) ∘ₗ
      K.liftBilin (modDatum S T 𝔪 Ψ (polyVector _ (Q i.1 i.2))) ∘ₗ inclusion inf_le_left
  have integrable (ψ : rapidOfLevel S N) :
      Integrable fun h : GInf E s ↦ holMinorsPi s u h * ψ.1 (x * (h, 1)) := by
    obtain ⟨⟨⟨h_cont, -⟩, h_decay⟩, -⟩ := ψ.2
    exact (IsBoundedMeasurable.of_continuous h_decay.bounded h_cont).integrable_mul_comp h_int _
  let ℓ : rapidOfLevel S N →ₗ[ℂ] ℂ :=
    { toFun ψ := realConv (holMinorsPi s u) ψ.1 x
      map_add' ψ ψ' := by simp [realConv, mul_add, integral_add, integrable]
      map_smul' z ψ := by simp [realConv, mul_left_comm (holMinorsPi s u _) z, integral_const_mul] }
  suffices ker_le : ⨅ i : StdClasses (principalLevel n' N) × ι, (L i).ker ≤ ℓ.ker by
    obtain ⟨a, ha⟩ : ∃ a : StdClasses (principalLevel n' N) × ι → ℂ, ∑ i, a i • L i = ℓ :=
      (mem_span_range_iff_exists_fun ℂ).1 (mem_span_of_iInf_ker_le_ker ker_le)
    refine ⟨a, fun ψ hψ ↦ ?_⟩
    have h_L (i : StdClasses (principalLevel n' N) × ι) : L i ⟨ψ, hψ⟩ =
        ∫ g : G E s, modKernelStdSpace S c b 𝔪 Ψ (Q i.1 i.2) g i.1.out * ψ g ∂S.quotMeasure := rfl
    simpa [mul_comm (ψ _), h_L, ℓ, realConv, Ψ] using (LinearMap.congr_fun ha ⟨ψ, hψ⟩).symm
  rintro ⟨ψ, hψ⟩ h_ker
  have lift_zero : lift K (modDatum S T 𝔪 Ψ (polyVector _ Q₀)) ψ = 0 :=
    lift_modDatum_eq_zero_of_mem_span hN S hc e Q h_span (Submodule.mem_inf.1 hψ).1 fun p i ↦
      (mem_iInf _).1 h_ker (p, i)
  have conv_zero : realConv (holMinorsPi s u) ψ = 0 :=
    realConv_holMinorsPi_eq_zero_of_lift_eq_zero ho hN h𝔪 S hb h_dom h_int h_rank e hQ₀_ne hQ₀_hol
      hψ lift_zero
  exact congrFun conv_zero x

end New.Rows
