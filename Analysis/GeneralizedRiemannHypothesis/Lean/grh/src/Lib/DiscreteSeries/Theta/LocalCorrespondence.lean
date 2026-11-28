import Lib.DiscreteSeries.Rigidity.KernelFixes
import Lib.DiscreteSeries.Theta.CasimirComparison
import Lib.DiscreteSeries.Theta.FockJointHarmonics
import Lib.Weil.Fock.OscillatorPair

/-!
# Existence of joint harmonics, Howe's argument and the local theta correspondence

This file works in the polynomial (Fock) model of a dual pair of unitary groups. For matching
parameters, a joint harmonic is built as a product of minors along layers. For an oscillator pair,
the projection of a joint harmonic by the discrete series kernel is then nonzero, is fixed by
`π'(f)` for functions `f` that reproduce the kernel of the second group, and generates all projected
polynomial vectors under bump functions of the second group.

## Main definitions and results

* `New.IsLayering`: finitely many layers, each a list of rows paired with columns, of weight `ν`.
* `New.IsMatch.isLayering`: for matching parameters (`New.IsMatch`) the sets of variables
  `New.FockDualPair.Layer` are layers of weight `New.HCParam.lowestKType l`.
* `New.IsMatch.exists_isJointHarmonic`: hence a joint harmonic (`New.IsJointHarmonic`) exists.
* `New.IsJointHarmonic.howe_argument`: in the polynomial (Fock) model with its row action
  `T.oscRows` and column action `T.swap.oscRows`, a subspace that is stable under the columns,
  contains a joint harmonic (`New.IsJointHarmonic`) and contains certain images of the row operators
  is the whole space.
* `New.OscillatorPair.re_inner_integratedRep_pos`: for a joint harmonic `Φ` and `Φ₁ = π(e_λ) Φ`,
  with `e_λ` the discrete series kernel, `⟨Φ, Φ₁⟩` has positive real part.
* `New.OscillatorPair.integratedRep_integratedRep_eq_self`: `π'(f) Φ₁ = Φ₁` for every `f` of
  suitable decay that reproduces `e_λ'`; the proof compares the Casimir operators of the two groups
  on `Φ` and uses `New.integratedRep_fix_of_isKHighest`.
* `New.OscillatorPair.exists_bump_integratedRep_eq`: every `π(e_λ) P` is obtained from `Φ₁` by a
  bump function of the second group; the proof rests on `New.IsJointHarmonic.howe_argument`.

Notions from other files:
* `New.HCParam.IsKHighest`: each matrix unit `E a a` acts on `x` by `ν a`, and `x` is killed by the
  compact raising operators, the `E a b` with `ε a = ε b` and `l b < l a`.
* `New.IsJointHarmonic`: `l` and `l'` match (`New.IsMatch`), and `Φ ≠ 0` is highest for rows and
  columns, of the weights of the two lowest `K`-types, and harmonic along rows and columns.
* `New.OscillatorPair`: two commuting oscillator representations on one Fock space, one acting on
  the rows and one on the columns.
* `New.pairSign`: the sign `σ * ε r * ε' c` of the variable in row `r` and column `c`, with
  `σ = T.globalSign`; `T.varSign (r, c)` is this sign.
* `New.FockDualPair.IsMatchedPair`: the row `r` is matched with the column `c`: with `n = card R`,
  `n' = card C`, `γ = T.rowShift`, `γ' = T.columnShift` and `a = l r - 2γ + n'`, one
  has `a = -(l' c - 2γ' + n)` and `|n - n'| < σ * ε r * ε' c * a`.
* `New.HCParam.lowestKType`: the integer vector Λ = λ+ρ−2ρ_c for a parameter l = 2λ, the highest
  weight of the lowest K-type.

## Relation to the literature

Known result: Theta correspondence of discrete series for real unitary dual pairs, with joint
harmonics. Only matched parameters with large gaps on Fock space are treated. The joint harmonic
exists and is unique up to scalar, and its projection is fixed by the partner's `π'(f)` for every
`f` of suitable decay that reproduces the partner's discrete series kernel. The projection of every
polynomial vector is a compactly supported smoothing, under the second group, of the projected joint
harmonic. Source: J.-S. Li, Theta lifting for unitary representations with nonzero cohomology, Duke
Math. J. 61 (1990) 913-937; R. Howe, Transcending classical invariant theory, J. Amer. Math. Soc. 2
(1989); A. Paul, First occurrence for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999)
636-657, Theorem 2.7.
-/

/-!
## Products of minors along layers and existence of joint harmonics

Existence of joint harmonics in the Fock model `T` of a dual pair of unitary groups. Polynomials in
the variables `X (T.varEquiv (r, c))` carry two actions. `New.FockDualPair.oscRows` is an action of
`gl R` (rows `r`, signs `ε`). `New.FockDualPair.vacuumWeight` is the weight of the vacuum `1`.
`New.FockDualPair.IsTermwiseHarmonic` forbids, in a monomial, two variables in one column from rows
of opposite signs; for `T.swap` it is the same with rows and columns exchanged.

A matched pair (row `r`, column `c`) occurs in `|New.FockDualPair.relWeight l r|` layers, one at
each level below that number. The signs cut the variables into four quadrants; the layers of one
pair of signs are nested and give the leading minors of that quadrant.
-/

section JointHarmonicExists

namespace New

open Matrix MvPolynomial Finset Units DiscreteSeries Function Fischer

variable {L : Type*} [Fintype L] {I : L → Type} [∀ t : L, Fintype (I t)]
  [∀ t : L, DecidableEq (I t)] {R C : Type} [Fintype C] [DecidableEq C]
  {ε : R → ℤˣ} {ε' : C → ℤˣ} {ι : Type} [Fintype ι] {T : FockDualPair ε ε' ι} {l ν : HCParam ε}
  {l' ν' : HCParam ε'} {ρ : (t : L) → I t → R} {κ : (t : L) → I t → C}

/-- A derivation of a polynomial ring sends a finite product to the sum of the products in which
one factor is replaced by its derivative. -/
theorem derivation_apply_prod {α : Type*} [DecidableEq α]
    (D : Derivation ℂ (MvPolynomial R ℂ) (MvPolynomial R ℂ)) (s : Finset α)
    (f : α → MvPolynomial R ℂ) :
    D (s.prod f) = ∑ i ∈ s, s.prod (update f i (D (f i))) := by
  induction s using cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have h_tail : ∀ i ∈ s, (cons a s ha).prod (update f i (D (f i))) =
        f a * s.prod (update f i (D (f i))) := fun i hi ↦ by grind
    calc D ((cons a s ha).prod f) = D (f a) * s.prod f + f a * D (s.prod f) := by
          simp [prod_cons, D.leibniz, mul_comm, add_comm, -cons_eq_insert]
      _ = D (f a) * s.prod f + ∑ i ∈ s, f a * s.prod (update f i (D (f i))) := by rw [ih, mul_sum]
      _ = ∑ i ∈ cons a s ha, (cons a s ha).prod (update f i (D (f i))) := by
          rw [sum_cons, prod_cons, update_self, prod_update_of_notMem ha, sum_congr rfl h_tail]

/-- If a derivation `D` acts on the columns of each matrix `M t` of polynomials through the matrix
`N t` (column `i` goes to `∑ j, N t i j •` column `j`), then it multiplies `∏ t, det (M t)` by
the sum of the traces of the `N t`. -/
theorem derivation_prod_det (D : Derivation ℂ (MvPolynomial R ℂ) (MvPolynomial R ℂ))
    (N M : (t : L) → Matrix (I t) (I t) (MvPolynomial R ℂ))
    (h_col : ∀ (t : L) (i k : I t), D (M t k i) = ∑ j : I t, N t i j • M t k j) :
    D (∏ t : L, det (M t)) = (∑ t : L, ∑ i : I t, N t i i) * ∏ t : L, det (M t) := by
  -- Each determinant is an eigenvector of `D` with eigenvalue the trace of `N t`; by the Leibniz
  -- rule the eigenvalues add up on the product.
  have h_det {t : L} : D (M t).det = ∑ i : I t, N t i i • (M t).det := by
    -- Expanding the determinant, `D` acts on one column at a time; replacing column `i` by a
    -- combination of the columns scales the determinant by `N t i i`.
    calc D (M t).det = ∑ i, ((M t).updateCol i fun k : I t ↦ ∑ j : I t, N t i j • M t k j).det := by
          simp +contextual [det_apply', updateCol, update_apply, mul_sum, derivation_apply_prod,
            h_col, sum_comm (α := I t)]
      _ = ∑ i : I t, N t i i • (M t).det := by simp only [det_updateCol_sum]
  induction (univ : Finset L) using cons_induction with
  | empty => simp
  | cons t s ht ih =>
    simp only [prod_cons, D.leibniz, ih, h_det, sum_cons, _root_.smul_eq_mul, ← sum_mul]
    ring

variable [DecidableEq R]

/-- Finitely many layers `t`, each pairing distinct rows `ρ t` with columns `κ t`. Layers that share
a row have columns of one sign. With each of its rows a layer contains all rows of the same sign as
that row that lie further out in `l` than it, in the direction given by the sign
`New.FockDualPair.varSign` of its variable in that layer. The total weight is `ν`. -/
structure IsLayering (T : FockDualPair ε ε' ι) (l ν : HCParam ε) (ρ : (t : L) → I t → R)
    (κ : (t : L) → I t → C) : Prop where
  /-- The rows of a layer are distinct. -/
  injective (t : L) : Injective (ρ t)
  /-- Two layers (possibly the same) that share a row have all their columns of one sign. -/
  sign_eq (t u : L) (i : I t) (j : I u) (k : I t) (m : I u) :
      ρ t i = ρ u j → ε' (κ t k) = ε' (κ u m)
  /-- A layer with the row `ρ t i` has every row `r` of the same sign with `l r > l (ρ t i)` if
  `New.FockDualPair.varSign` is `1` at `(ρ t i, κ t i)`, with `l r < l (ρ t i)` if it is `-1`. -/
  closed (t : L) (i : I t) (r : R) :
      ε r = ε (ρ t i) → 0 < T.varSign (ρ t i, κ t i) * (l r - l (ρ t i)) → ∃ j : I t, ρ t j = r
  /-- The weight `ν r` is that of the vacuum plus the signs `New.FockDualPair.varSign` at the pairs
  `(r, κ t i)`, over all `(t, i)` with row `ρ t i = r`. -/
  weight_eq (r : R) :
      ν r = T.vacuumWeight (ε r) + ∑ t : L, ∑ i : I t with ρ t i = r, (T.varSign (r, κ t i)).1

omit [Fintype ι] in
/-- Let `(ρ, κ)` be layers and let `P` be the product of their minors, with the matrices transposed.
If `a = b`, or `a` has the sign of `b` and lies further out than `b` in the direction `s`, then the
polarisation `∑ X (a, c) * ∂P/∂X (b, c)`, over the columns `c` where the variable `(b, c)` has sign
`s`, is `P` times the number of `(t, i)` with `ρ t i = a = b` and `T.varSign (b, κ t i) = s`. -/
theorem IsLayering.polarisation_prod_det (H : IsLayering T l ν ρ κ) {P : MvPolynomial ι ℂ}
    (hP : P = ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ)
    (a b : R) (s : ℤˣ) (hε : ε a = ε b) (hab : a = b ∨ s * l b < s * l a) :
    T.polarisation P a b s =
      (∑ t : L, ∑ i : I t,
        if ρ t i = b ∧ ρ t i = a ∧ T.varSign (b, κ t i) = s then 1 else 0) * P := by
  classical
  -- The polarisation is a derivation, so `derivation_prod_det` applies.
  let D : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
    .mk' (∑ c with T.varSign (b, c) = s,
        (X (T.varEquiv (a, c)) : MvPolynomial ι ℂ) • (pderiv (T.varEquiv (b, c))).toLinearMap)
      (by simp [mul_sum, ← sum_add_distrib, mul_add, mul_left_comm])
  -- In each layer `D` sends row `b` to row `a` or to zero, and kills the other rows.
  have hD (t : L) (i k : I t) : D (X (T.varEquiv (ρ t i, κ t k))) =
      ∑ j : I t, (if ρ t i = b ∧ ρ t j = a ∧ T.varSign (b, κ t i) = s
        then (1 : MvPolynomial ι ℂ) else 0) • X (T.varEquiv (ρ t j, κ t k)) := by
    have h_col_sign : ε' (κ t k) = ε' (κ t i) := H.sign_eq t t i i k i rfl
    obtain ⟨j, rfl⟩ | ha := em (∃ j : I t, ρ t j = a)
    · simp [D, (H.injective t).eq_iff, pairSign, h_col_sign, Pi.single_apply, ite_and]
    · -- row `a` is missing, so by `H.closed` row `b` is missing too or has the wrong sign
      have h_wrong_sign : ρ t i = b → T.globalSign * ε b * ε' (κ t i) ≠ s := fun hb hs ↦ hab.elim
        (fun h_eq ↦ ha ⟨i, hb.trans h_eq.symm⟩) fun h_out ↦
          ha (H.closed t i a (by rw [hb, hε]) (by simpa [hb, hs, pairSign, mul_sub] using h_out))
      simp +contextual [D, pairSign, Pi.single_apply, ite_and, not_exists.1 ha, h_col_sign,
        h_wrong_sign]
  simpa [D, hP, FockDualPair.polarisation, -sum_boole] using
    derivation_prod_det D _ (fun t : L ↦ (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ) hD

variable [Fintype R]

omit [Fintype ι] in
/-- Let `(ρ, κ)` be a layering of weight `ν` for `l`: finitely many layers `t`, each pairing
distinct rows `ρ t` with columns `κ t`, such that layers sharing a row have columns of one sign,
each layer contains with each of its rows all rows of the same sign lying further out in `l` in the
direction of the sign of its variable, and the total weight is `ν`. The product `P` over `t` of the
minors of the variables with rows `ρ t` and columns `κ t`, written here with the transposed
matrices, is `K`-highest of weight `ν` for the row action `T.oscRows` and `l`. Also, no monomial of
`P` has two variables in one row whose columns have opposite signs. -/
theorem IsLayering.isKHighest_and_isTermwiseHarmonic (H : IsLayering T l ν ρ κ)
    {P : MvPolynomial ι ℂ}
    (hP : P = ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ) :
    l.IsKHighest T.oscRows ν P ∧ T.swap.IsTermwiseHarmonic P := by
  classical
  -- By `oscRows_E_eq_polarisation_sub` the compact matrix unit `E a b` is the polarisation for
  -- `a, b, 1` minus the one for `b, a, -1`, plus the weight of the vacuum if `a = b`. Both
  -- polarisations act on `P` by scalars (`IsLayering.polarisation_prod_det`).
  refine ⟨⟨fun a ↦ ?_, fun a b hε hl ↦ ?_⟩, fun a b c hε ↦ ?_⟩
  · -- weight: the two counts differ by the sum of signs in `H.weight_eq`
    have h_sign (t : L) (i : I t) :
        ((if ρ t i = a then if T.varSign (a, κ t i) = 1 then 1 else 0 else 0) -
            if ρ t i = a then if T.varSign (a, κ t i) = -1 then 1 else 0 else 0 :
            MvPolynomial ι ℂ) =
          MvPolynomial.C (if ρ t i = a then ((T.varSign (a, κ t i)).1 : ℂ) else 0) := by
      split_ifs <;> simp_all [Int.units_ne_iff_eq_neg]
    -- so the difference of the two counts is the sum of the signs
    rw [oscRows_E_eq_polarisation_sub rfl, H.polarisation_prod_det hP a a 1 rfl (.inl rfl),
      H.polarisation_prod_det hP a a (-1) rfl (.inl rfl), ← sub_mul]
    simp [← sum_sub_distrib, sum_filter, h_sign, ite_and, -sum_boole, H.weight_eq, ← C_mul',
      ← add_mul, add_comm]
  · -- raising operators: `a ≠ b`, so both counts vanish
    have hne : a ≠ b := fun h ↦ hl.ne (by rw [h])
    simp +contextual [oscRows_E_eq_polarisation_sub hε, hne, hne.symm, ite_and,
      H.polarisation_prod_det hP a b 1 hε (.inr (by simpa using hl)),
      H.polarisation_prod_det hP b a (-1) hε.symm (.inr (by simpa using hl))]
  · have h_absent (x : R × C) (hx : ∀ (t : L) (i j : I t), (ρ t i, κ t j) ≠ x) :
        pderiv (T.varEquiv x) P = 0 := by
      simp [hP, hx, derivation_prod_det _ 0]
    change pderiv (T.varEquiv (c, a)) (pderiv (T.varEquiv (c, b)) P) = 0
    -- by `H.sign_eq` one of the variables `(c, a)`, `(c, b)` does not occur
    by_cases h_occurs : ∃ (t : L) (i j : I t), (ρ t i, κ t j) = (c, b)
    · obtain ⟨t, i, j, h_eq⟩ := h_occurs
      rw [pderiv_comm, h_absent (c, a) fun u k m h_eq' ↦ hε (by grind [H.sign_eq u t k i m j]),
        map_zero]
    · rw [h_absent (c, b) fun t i j h_eq ↦ h_occurs ⟨t, i, j, h_eq⟩, map_zero]

omit [Fintype ι] in
/-- Let `(ρ, κ)` be layers of weight `ν` for the rows and `(κ, ρ)` layers of weight `ν'` for the
columns. Then the product over `t` of the minors of the variables with rows `ρ t` and columns `κ t`
is nonzero, highest of weight `ν` for the rows and `ν'` for the columns, and harmonic both ways. -/
theorem IsLayering.isJointHighest_prod_det (H : IsLayering T l ν ρ κ)
    (h_swap : IsLayering T.swap l' ν' κ ρ) :
    T.IsJointHighest l l' (∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j))))
      ν ν' := by
  set P : MvPolynomial ι ℂ := ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))
    with hP
  have h_ne : P ≠ 0 := by
    -- Each minor is the generic determinant with its variables renamed injectively.
    have h_inj (t : L) : Injective (T.varEquiv ∘ Prod.map (ρ t) (κ t)) :=
      T.varEquiv.injective.comp ((H.injective t).prodMap (h_swap.injective t))
    have h_minor (t : L) :
        rename (T.varEquiv ∘ Prod.map (ρ t) (κ t)) (mvPolynomialX (I t) (I t) ℂ).det ≠ 0 :=
      (map_ne_zero_iff _ (rename_injective _ (h_inj t))).2 (det_mvPolynomialX_ne_zero (I t) ℂ)
    simpa [hP, prod_eq_zero_iff, det_apply] using h_minor
  -- `IsLayering.isKHighest_and_isTermwiseHarmonic` applies to the columns as it stands, and to the
  -- rows after transposing the minors.
  obtain ⟨h_col_highest, h_col_harmonic⟩ := h_swap.isKHighest_and_isTermwiseHarmonic hP
  obtain ⟨h_row_highest, h_row_harmonic⟩ :=
    H.isKHighest_and_isTermwiseHarmonic (P := P) (by simp only [hP, det_transpose])
  exact ⟨h_ne, h_col_highest, h_col_harmonic, h_row_highest, h_row_harmonic⟩

omit [Fintype ι] in
/-- Version of `IsLayering.isJointHighest_prod_det` for a polynomial `P` that is given as the
product of the minors: `P` is nonzero, highest of weight `ν` for the rows and `ν'` for the columns,
and harmonic both ways. -/
theorem IsLayering.isJointHighest_of_eq_prod_det (H : IsLayering T l ν ρ κ)
    (h_swap : IsLayering T.swap l' ν' κ ρ) {P : MvPolynomial ι ℂ}
    (hP : P = ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))) :
    T.IsJointHighest l l' P ν ν' := by
  subst hP
  exact H.isJointHighest_prod_det h_swap

omit [DecidableEq R] [DecidableEq C] [Fintype ι] in
/-- Let the parameters `l` and `l'` match: each row and each column is either matched, that is, its
centred parameter (`l r - 2 γ + card C` for a row) is large and opposite to that of its partner, or
has a small one. Then a row `r` of nonzero weight `T.relWeight l r` (the lowest `K`-type relative to
the vacuum) is matched with a column `c`, and the weight has the sign of the variable `(r, c)`. -/
theorem IsMatch.exists_isMatchedPair_of_relWeight_ne_zero (hm : IsMatch T l l') {r : R}
    (h_ne : T.relWeight l r ≠ 0) :
    ∃ c : C, T.IsMatchedPair l l' r c ∧ T.varSign (r, c) = (T.relWeight l r).sign := by
  obtain ⟨c, h_pair⟩ | h_free := hm.left r
  · have h_large : (Fintype.card C - Fintype.card R : ℤ) <
        T.varSign (r, c) * T.centredParam l r := by
      linarith [h_pair.right, neg_le_abs (Fintype.card R - Fintype.card C : ℤ)]
    have h_sign : 0 ≤ T.varSign (r, c) * T.relWeight l r :=
      hm.sign_mul_relWeight_nonneg r (T.varSign (r, c)) h_large
    refine ⟨c, h_pair, ?_⟩
    obtain h_var | h_var := Int.units_eq_one_or (T.varSign (r, c)) <;> rw [h_var] at h_sign ⊢ <;>
      grind [Units.val_neg, val_one]
  · -- an unmatched row has weight both `≥ 0` and `≤ 0`
    have h_nonneg : 0 ≤ T.relWeight l r := by
      simpa using hm.sign_mul_relWeight_nonneg r 1 (by simp; linarith [abs_lt.1 h_free])
    have h_nonpos : T.relWeight l r ≤ 0 := by
      simpa using hm.sign_mul_relWeight_nonneg r (-1) (by simp; linarith [abs_lt.1 h_free])
    exact absurd (h_nonpos.antisymm h_nonneg) h_ne

omit [DecidableEq R] [DecidableEq C] [Fintype ι] in
/-- Let the row `r` be matched with the column `c` and have nonzero weight `T.relWeight l r`. A row
`r'` of the same sign that lies further out in `l`, in the direction of the sign of the variable
`(r, c)`, is matched with a column of the sign of `c`, and its weight is at least as large in
absolute value. -/
theorem IsMatch.exists_isMatchedPair_of_outer (hm : IsMatch T l l') {r r' : R} {c : C}
    (h_pair : T.IsMatchedPair l l' r c) (h_ne : T.relWeight l r ≠ 0) (h_row : ε r' = ε r)
    (h_out : 0 < T.varSign (r, c) * (l r' - l r)) :
    ∃ c' : C, T.IsMatchedPair l l' r' c' ∧ ε' c' = ε' c ∧
      (T.relWeight l r).natAbs ≤ (T.relWeight l r').natAbs := by
  -- The highest weight of the lowest `K`-type is dominant for the order of `l`.
  have h_dom : ∀ a b : R, ε a = ε b → l b < l a → l.lowestKType b ≤ l.lowestKType a := by
    simpa [IsKDominant] using hm.hasGap_row.isKDominant_lowestKType
  obtain ⟨c₀, h_pair₀, h_sign⟩ := hm.exists_isMatchedPair_of_relWeight_ne_zero h_ne
  obtain rfl : c₀ = c := hm.col_eq_of_isMatchedPair h_pair₀ h_pair
  -- By `h_dom` the weight moves in the direction of its sign.
  have h_mono : T.varSign (r, c₀) * T.relWeight l r ≤ T.varSign (r, c₀) * T.relWeight l r' := by
    grind [h_dom r r', h_dom r' r]
  have h_same_sign : (T.relWeight l r').sign = (T.relWeight l r).sign := by grind
  obtain ⟨c', h_pair', h_sign'⟩ :=
    hm.exists_isMatchedPair_of_relWeight_ne_zero (r := r') (by grind)
  have h_var : T.varSign (r', c') = T.varSign (r, c₀) :=
    Units.ext (h_sign'.trans (h_same_sign.trans h_sign.symm))
  exact ⟨c', h_pair', by simpa [pairSign, h_row] using h_var, by grind⟩

namespace FockDualPair

variable (T) (s : Equiv.Perm (ℤˣ × ℤˣ)) (w : ι → ℕ) (t : Fin (univ.sup w) × ℤˣ × ℤˣ)

/-- The layer `t` for the heights `w` of the variables. Here `t` is a level below the largest height
together with a pair of signs. The layer consists of the variables of height above that level whose
signs `(ε r, ε' c)`, for row `r` and column `c`, are sent to that pair by `s`. -/
abbrev Layer : Type :=
  {x : ι // t.1 < w x ∧ s ((T.varEquiv.symm x).map ε ε') = t.2}

/-- The row of a variable of the layer `t`. -/
def layerRow (x : T.Layer s w t) : R := (T.varEquiv.symm x).1

/-- The column of a variable of the layer `t`. -/
def layerCol (x : T.Layer s w t) : C := (T.varEquiv.symm x).2

variable {T s w t}

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem varEquiv_layerRow_layerCol (x : T.Layer s w t) :
    T.varEquiv (T.layerRow s w t x, T.layerCol s w t x) = x :=
  T.varEquiv.apply_symm_apply x

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem sign_layerCol_eq (x y : T.Layer s w t) :
    ε' (T.layerCol s w t x) = ε' (T.layerCol s w t y) :=
  congrArg Prod.snd (s.injective (x.property.right.trans y.property.right.symm))

end FockDualPair

omit [DecidableEq C] in
/-- Let `l = 2λ`, `l' = 2λ'` match (`IsMatch`): with `n = card R` and `n' = card C` both have gap
`500(n+n')³`, and with `ξ r = λ r − γ + n'/2` and `ξ' c = λ' c − γ' + n/2`, rows and columns pair
off as `ξ r = −ξ' c` with `σ ε r ε' c ξ r > |n−n'|/2`, the rest having small `|ξ|`. Let the height
`w` of the variable of `(r, c)` be `|T.relWeight l r|` (row-`r` entry of the lowest `K`-type minus
the vacuum weight) if `(r, c)` is matched, and `0` otherwise. Then the layers, with rows
`T.layerRow s w` and columns `T.layerCol s w`, form an `IsLayering` of weight `l.lowestKType`. The
permutation `s` of the pairs of signs lets the rows and the columns use the same layers. -/
theorem IsMatch.isLayering (hm : IsMatch T l l') (s : Equiv.Perm (ℤˣ × ℤˣ)) (w : ι → ℕ)
    (hw : ∀ (r : R) (c : C),
      w (T.varEquiv (r, c)) = if T.IsMatchedPair l l' r c then (T.relWeight l r).natAbs else 0) :
    IsLayering T l l.lowestKType (T.layerRow s w) (T.layerCol s w) := by
  -- The variable `(r, c)` lies in a layer of level `m` exactly when the pair is matched and
  -- `m < |T.relWeight l r|`.
  have h_level (r : R) (c : C) (m : ℕ) :
      m < w (T.varEquiv (r, c)) ↔ T.IsMatchedPair l l' r c ∧ m < (T.relWeight l r).natAbs := by
    grind
  have h_mem {t : Fin (univ.sup w) × ℤˣ × ℤˣ} (x : T.Layer s w t) {r : R}
      (h_row : T.layerRow s w t x = r) :
      T.IsMatchedPair l l' r (T.layerCol s w t x) ∧ t.1 < (T.relWeight l r).natAbs := by
    rw [← h_level, ← h_row, FockDualPair.varEquiv_layerRow_layerCol]
    exact x.property.left
  -- Variables of layers with the same row have the same column, so they are equal.
  have h_col {t u : Fin (univ.sup w) × ℤˣ × ℤˣ} {x : T.Layer s w t} {y : T.Layer s w u}
      (h_row : T.layerRow s w t x = T.layerRow s w u y) :
      T.layerCol s w t x = T.layerCol s w u y :=
    hm.col_eq_of_isMatchedPair (h_mem x h_row).left (h_mem y rfl).left
  have h_var {t u : Fin (univ.sup w) × ℤˣ × ℤˣ} {x : T.Layer s w t} {y : T.Layer s w u}
      (h_row : T.layerRow s w t x = T.layerRow s w u y) : (x : ι) = y := by
    grind [FockDualPair.varEquiv_layerRow_layerCol]
  refine ⟨fun t x y h_row ↦ Subtype.ext (h_var h_row), fun t u x y x' y' h_row ↦ by
    rw [FockDualPair.sign_layerCol_eq x' x, h_col h_row, FockDualPair.sign_layerCol_eq y y'],
    ?_, fun r ↦ ?_⟩
  · -- A row further out is matched with a column of the same sign and reaches the same level.
    intro t x r' h_row h_out
    obtain ⟨h_pair, h_lt⟩ := h_mem x rfl
    obtain ⟨c', h_pair', h_sign, h_le⟩ :=
      hm.exists_isMatchedPair_of_outer h_pair (by lia) h_row h_out
    exact ⟨⟨T.varEquiv (r', c'), (h_level r' c' t.1).2 ⟨h_pair', h_lt.trans_le h_le⟩, by
      simpa [h_row, h_sign, FockDualPair.layerRow, FockDualPair.layerCol, Prod.map] using
        x.property.right⟩,
      by simp [FockDualPair.layerRow]⟩
  · -- The indices with row `r` correspond, by their level, to the numbers below
    -- `|T.relWeight l r|`, and each adds the sign of `T.relWeight l r`.
    trans T.vacuumWeight (ε r) + ∑ _m ∈ range (T.relWeight l r).natAbs, (T.relWeight l r).sign
    · rw [sum_const, card_range, nsmul_eq_mul, mul_comm, Int.sign_mul_natAbs, add_sub_cancel]
    rw [add_right_inj, sum_sigma', eq_comm]
    refine sum_of_injOn (fun ⟨t, _⟩ ↦ (t.1 : ℕ)) ?_ ?_ ?_ ?_
    · -- the level determines the index
      rintro ⟨t, x⟩ hx ⟨u, y⟩ hy h_eq
      simp only [Finset.mem_coe, mem_sigma, mem_filter, mem_univ, true_and] at hx hy
      have h_xy : (x : ι) = y := h_var (hx.trans hy.symm)
      obtain rfl : t = u :=
        Prod.ext (Fin.ext h_eq) (by rw [← x.property.right, ← y.property.right, h_xy])
      rw [Subtype.ext h_xy]
    · -- the level lies below `|T.relWeight l r|`
      exact fun ⟨t, x⟩ hx ↦ by simpa using (h_mem x (r := r) (by simpa using hx)).right
    · -- every level below `|T.relWeight l r|` occurs, at the column matched with `r`
      intro m h_range h_missing
      obtain ⟨c, h_pair, -⟩ :=
        hm.exists_isMatchedPair_of_relWeight_ne_zero (r := r) (by grind)
      have h_height : m < w (T.varEquiv (r, c)) := (h_level r c m).2 ⟨h_pair, mem_range.1 h_range⟩
      let x : T.Layer s w (⟨m, h_height.trans_le (le_sup (mem_univ _))⟩, s (ε r, ε' c)) :=
        ⟨T.varEquiv (r, c), h_height, by simp⟩
      have h_row : T.layerRow s w _ x = r := by simp [x, FockDualPair.layerRow]
      exact absurd ⟨⟨_, x⟩, by simpa using h_row, rfl⟩ h_missing
    · -- the sign of the variable is that of the weight
      rintro ⟨t, x⟩ hx
      obtain ⟨h_pair, h_lt⟩ := h_mem x (r := r) (by simpa using hx)
      obtain ⟨c, h_pair', h_sign⟩ := hm.exists_isMatchedPair_of_relWeight_ne_zero (r := r) (by lia)
      rwa [hm.col_eq_of_isMatchedPair h_pair' h_pair] at h_sign

/-- If the parameters `l = 2λ`, `l' = 2λ'` match, there is a joint harmonic. With `n = card R` and
`n' = card C`, matching means that both have gap `500(n+n')³`, and the entries
`ξ r = λ r − γ + n'/2`, `ξ' c = λ' c − γ' + n/2` pair off as `ξ r = −ξ' c` with
`σ ε r ε' c ξ r > |n−n'|/2`, the rest having small `|ξ|`. A joint harmonic is a nonzero polynomial
that is highest of weights `New.HCParam.lowestKType l` for the rows and
`New.HCParam.lowestKType l'` for the columns, and satisfies `New.FockDualPair.IsTermwiseHarmonic`
along columns and along rows (for `T` and `T.swap`).

This is the existence part of the known correspondence of discrete series by joint harmonics. -/
theorem IsMatch.exists_isJointHarmonic (hm : IsMatch T l l') :
    ∃ Φ : MvPolynomial ι ℂ, IsJointHarmonic T l l' Φ := by
  classical
  -- Take the product of the minors of the layers of `IsMatch.isLayering`. The same layers serve
  -- for the columns, with the two signs exchanged.
  let w : ι → ℕ := fun x ↦ let (r, c) := T.varEquiv.symm x
    if T.IsMatchedPair l l' r c then (T.relWeight l r).natAbs else 0
  have h_rows (r : R) (c : C) : w (T.varEquiv (r, c)) =
      if T.IsMatchedPair l l' r c then (T.relWeight l r).natAbs else 0 := by simp [w]
  have h_opposite (r : R) (c : C) (h : T.IsMatchedPair l l' r c) :
      (T.relWeight l r).natAbs = (T.swap.relWeight l' c).natAbs := by
    rw [hm.relWeight_eq_neg h, Int.natAbs_neg]
  -- Both sides assign the same height to a variable, as matched weights are opposite.
  have h_cols (c : C) (r : R) : w (T.swap.varEquiv (c, r)) =
      if T.swap.IsMatchedPair l' l c r then (T.swap.relWeight l' c).natAbs else 0 := by
    refine (h_rows r c).trans ?_
    grind [pairSign, int_unit_val_eq_one_or_neg_one, val_mul, Units.val_neg]
  have h_col_layers : IsLayering T.swap l' l'.lowestKType (T.layerCol 1 w) (T.layerRow 1 w) :=
    hm.swap.isLayering (Equiv.prodComm ℤˣ ℤˣ) w h_cols
  exact ⟨_, hm, (hm.isLayering 1 w h_rows).isJointHighest_prod_det h_col_layers⟩

end New

end JointHarmonicExists

/-!
## Howe's argument in Fock space

The proof is an induction on the degree with the Fischer inner product, ending in the uniqueness of
the joint harmonic.
-/

section HoweArgument

open New MvPolynomial Submodule Int Fischer DiscreteSeries Fock

variable {R C ι : Type} [Fintype R] [Fintype C] {ε : R → ℤˣ} {ε' : C → ℤˣ}
  {T : FockDualPair ε ε' ι} {l : HCParam ε} {l' : HCParam ε'}

omit [Fintype R] in
/-- For rows `a` and `b` with `ε a ≠ ε b`: if row `b` of `Q` has no variable of sign `1`, or row `a`
has none of sign `-1`, then the Laplacian `T.fockLaplacian a b` kills `Q`. It is a sum, over the
columns `c` with `T.varSign (a, c) = -1`, of terms built from `∂/∂X(a,c) ∂/∂X(b,c)`. -/
theorem New.Fischer.fockLaplacian_eq_zero_of_pderiv_eq_zero {Q : MvPolynomial ι ℂ} {a b : R}
    (hab : ε a ≠ ε b)
    (h_pure : (∀ c : C, T.varSign (b, c) = 1 → pderiv (T.varEquiv (b, c)) Q = 0) ∨
      ∀ c : C, T.varSign (a, c) = -1 → pderiv (T.varEquiv (a, c)) Q = 0) :
    T.fockLaplacian a b Q = 0 := by
  rw [FockDualPair.fockLaplacian, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun c hc ↦ ?_
  have ha : T.varSign (a, c) = -1 := (Finset.mem_filter.1 hc).2
  have hb : T.varSign (b, c) = 1 := by
    rw [← neg_neg (1 : ℤˣ), ← ha]
    simp [units_ne_iff_eq_neg.1 hab, pairSign]
  suffices pderiv (T.varEquiv (a, c)) (pderiv (T.varEquiv (b, c)) Q) = 0 by
    simpa [glOp, ha, hb, raiseOp, lowerOp]
  rcases h_pure with h_row_b | h_row_a
  · rw [h_row_b c hb, map_zero]
  · rw [pderiv_comm, h_row_a c ha, map_zero]

/-- For matched parameters (each row is matched with a column or has a small centred parameter) and
`l b ≤ l a`, the centred parameter `l b - 2γ + card C` of row `b` is below `card R - card C` or that
of row `a` is above `card C - card R`. -/
theorem New.IsMatch.centredParam_lt_or_lt (hm : IsMatch T l l') {a b : R} (h_le : l b ≤ l a) :
    (Fintype.card C - Fintype.card R : ℤ) < -T.centredParam l b ∨
      (Fintype.card C - Fintype.card R : ℤ) < T.centredParam l a := by
  have h_centred_le : T.centredParam l b ≤ T.centredParam l a := by simpa using h_le
  have h_abs := neg_le_abs (Fintype.card R - Fintype.card C : ℤ)
  obtain ⟨c, -, h_large⟩ | h_free := hm.left a
  · -- Row `a` is matched: its centred parameter, times the sign of the variable, is large.
    rcases int_unit_val_eq_one_or_neg_one (T.varSign (a, c)) with h_sign | h_sign <;>
      rw [h_sign] at h_large
    · exact .inr (by linarith)
    · exact .inl (by linarith)
  · exact .inr (by linarith [(abs_lt.1 h_free).1])

variable [Fintype ι]

/-- If `G` does not contain all polynomials of degree at most `j`, then some nonzero one of them is
orthogonal to those in `G` for the Fischer inner product. -/
theorem New.Fischer.perpInDegree_ne_bot {j : ℤ} {G : Submodule ℂ (MvPolynomial ι ℂ)}
    (hj : ¬ polyDegreeLE j ≤ G) : perpInDegree j G ≠ ⊥ := by
  intro h_bot
  have h_split : polyDegreeLE j ⊓ G ⊔ perpInDegree j G = polyDegreeLE j :=
    sup_orthogonal_inf_of_hasOrthogonalProjection inf_le_left
  exact hj (by simpa [h_bot] using h_split)

/-- Let `Q` be highest of the weight `Λ` of the lowest `K`-type for the rows and harmonic for the
columns (each `T.swap.fockLaplacian c d` with `ε' c ≠ ε' d` kills `Q`). If `s` times the centred
parameter `l r - 2γ + card C` of row `r` exceeds `card C - card R`, then `Q` has no variable of sign
`-s` in that row. -/
theorem New.IsMatch.pderiv_eq_zero_of_lt_centredParam [DecidableEq C] [DecidableEq R]
    (hm : IsMatch T l l') {Q : MvPolynomial ι ℂ}
    (h_highest : l.IsKHighest T.oscRows l.lowestKType Q) (h_harm : T.swap.IsLaplaceHarmonic Q)
    (r : R) (s : ℤˣ) (hr : Fintype.card C - Fintype.card R < (s : ℤ) * T.centredParam l r)
    (c : C) (hc : T.varSign (r, c) = -s) : pderiv (T.varEquiv (r, c)) Q = 0 := by
  obtain ⟨h_weight, h_row⟩ := h_highest
  exact ((polarisation_eq_of_isCompactPrimitive hm.hasGap_row.injective h_row h_harm r s).2
    (h_weight r)
    (hm.sign_mul_relWeight_nonneg r s hr)).2 c hc

/-- Howe's argument: a column-stable subspace that contains a joint harmonic and the images (a)–(c)
below is the whole space.

Let `Φ` be a joint harmonic of the dual pair `T`, that is, a nonzero polynomial, highest of the
weights of the lowest `K`-types and harmonic for rows and columns. Let `G` be a space of polynomials
that is stable under the action `T.swap.oscRows` on the columns and contains `Φ`. Write `ρ` for the
action `T.oscRows` on the rows and `Λ` for `l.lowestKType`. Suppose that `G` contains
(a) `ρ X P` for every matrix `X` and every highest vector `P` of a weight `ν` with `ν - Λ` outside
`l.rootCone`, the cone of the positive roots,
(b) the images of the `E b a` with `ε a = ε b` and `l b < l a`,
(c) the images of the `E a a - Λ a`.
Then `G` is the whole space. -/
theorem New.IsJointHarmonic.howe_argument [DecidableEq C] [DecidableEq R] {Φ : MvPolynomial ι ℂ}
    (hΦ : IsJointHarmonic T l l' Φ) (G : Submodule ℂ (MvPolynomial ι ℂ))
    (hG_cols : ∀ Y : Matrix C C ℂ, G ∈ (T.swap.oscRows Y).invtSubmodule) (hΦ_mem : Φ ∈ G)
    (h_off_cone : ∀ (ν : R → ℤ) (P : MvPolynomial ι ℂ), l.IsKHighest T.oscRows ν P →
      ν - l.lowestKType ∉ l.rootCone → ∀ X : Matrix R R ℂ, T.oscRows X P ∈ G)
    (h_lower : ∀ a b : R, ε a = ε b → l b < l a →
      ∀ P : MvPolynomial ι ℂ, T.oscRows.E b a P ∈ G)
    (h_diag : ∀ (a : R) (P : MvPolynomial ι ℂ),
      T.oscRows.E a a P - (l.lowestKType a : ℂ) • P ∈ G) :
    G = ⊤ := by
  -- Induct on the degree. If `G` missed a polynomial of degree at most `j`, the orthogonal
  -- complement `perpInDegree j G` would contain a vector `Q ≠ 0` highest for the columns; it has
  -- all the properties that characterize the joint harmonic `Φ ∈ G` up to a scalar, so `Q ∈ G`
  -- and `Q = 0`.
  suffices h_deg : ∀ j : ℤ, polyDegreeLE j ≤ G by
    exact eq_top_iff'.2 fun P ↦ h_deg P.totalDegree fun d hd ↦ ofNat_le.2 (le_totalDegree hd)
  refine Int.strongRec (m := 0) (fun j hj_neg ↦ ?_) fun j _ ih ↦ ?_
  · have h_empty : {d : ι →₀ ℕ | (d.degree : ℤ) ≤ j} = ∅ := by ext; simp; lia
    simp [polyDegreeLE, restrictSupport_eq_span, h_empty]
  by_contra hj
  obtain ⟨-, Q, hQ, hQ_ne, -, h_col⟩ := l'.exists_highest_vector (ρ := T.swap.oscRows)
    (perpInDegree j G) (perpInDegree_ne_bot hj) fun _ _ hcd ↦ mapsTo_perpInDegree hcd (hG_cols _)
  -- `Q` is highest of weight `Λ` for the rows: take adjoints in `h_diag` and `h_lower`. If
  -- `E b a` maps `N` into `G`, then `E a b` maps the complement of `G` into that of `N`
  -- (`mapsTo_perpInDegree`).
  have h_weight (a : R) : T.oscRows.E a a Q = (l.lowestKType a : ℂ) • Q := by
    have h_stable : G ≤ G.comap (T.oscRows.E a a) :=
      fun P hP ↦ (G.sub_mem_iff_left (G.smul_mem _ hP)).1 (h_diag a P)
    exact sub_eq_zero.1 (eq_zero_of_mem_perpInDegree
      (sub_mem (mapsTo_perpInDegree rfl h_stable hQ) (smul_mem _ _ hQ)) (h_diag a Q))
  have h_row : T.oscRows.IsCompactPrimitive l Q := fun a b hab hl ↦
    eq_zero_of_mem_perpInDegree
      (mapsTo_perpInDegree hab (fun P _ ↦ h_lower a b hab hl P) hQ) mem_top
  have h_highest : l.IsKHighest T.oscRows l.lowestKType Q := ⟨h_weight, h_row⟩
  -- The Laplacians of the columns kill `Q` by Fischer's decomposition, as `G` is stable under the
  -- columns.
  have h_harm_col : T.swap.IsLaplaceHarmonic Q :=
    fun _ _ hcd ↦ fockLaplacian_eq_zero ih hQ hcd rfl fun h_mem ↦ hG_cols _ h_mem
  -- The Laplacians of the rows kill `Q`: it suffices to treat one whose value is a highest vector,
  -- of weight `Λ + e_a - e_b`.
  have h_harm_row : T.IsLaplaceHarmonic Q := by
    refine isLaplaceHarmonic_of_isKHighest h_highest fun a b hab h_highest' ↦ ?_
    by_cases h_cone :
        l.lowestKType + Pi.single a 1 - Pi.single b 1 - l.lowestKType ∈ l.rootCone
    · -- In the cone `l b ≤ l a` (pair with `-l`), so row `b` or row `a` of `Q` has variables of
      -- one sign only.
      have h_le : l b ≤ l a := by simpa [add_assoc] using h_cone (-l) (by simp)
      refine fockLaplacian_eq_zero_of_pderiv_eq_zero hab ?_
      have h_pure := hΦ.pderiv_eq_zero_of_lt_centredParam h_highest h_harm_col
      rcases hΦ.centredParam_lt_or_lt h_le with h_small | h_large
      · exact .inl fun c hc ↦ h_pure b (-1) (by simpa using h_small) c (by simpa using hc)
      · exact .inr (h_pure a 1 (by simpa using h_large))
    · -- Off the cone `h_off_cone` lets Fischer's decomposition apply again.
      exact fockLaplacian_eq_zero ih hQ hab rfl fun _ ↦ h_off_cone _ _ h_highest' h_cone _
  -- By uniqueness `Q = c • Φ`, so `Q ∈ G`.
  obtain ⟨c, rfl⟩ : ∃ c : ℂ, Q = c • Φ := hΦ.unique
    ⟨hQ_ne, h_col, h_harm_row, h_highest, h_harm_col⟩ hΦ.isJointHighest.isPreJointHarmonic
  exact hQ_ne (eq_zero_of_mem_perpInDegree hQ (G.smul_mem c hΦ_mem))

end HoweArgument

/-!
## The projected joint harmonic and the local theta correspondence

The analytic part of the local theta correspondence. Let `π`, `π'` be an oscillator pair on Fock
space (`New.OscillatorPair`), `Φ` a joint harmonic of parameters `l`, `l'`
(`New.IsJointHarmonic`), and `Φ₁ = π(e_λ) Φ`, where `π(f) = ∫ f g • π g` is
`New.integratedRep π f`, `e_λ` is `New.HCParam.dsKernel l` (the signs come from the type of `l`),
and a polynomial is read as a vector of Fock space by `New.Fock.polyVector`.

The results are stated for the projection `π(e_λ)` of the first group, which acts on the rows; those
for the second group follow by `New.OscillatorPair.swap`. To work with `-λ` in place of `λ`, apply
them to the parameters `-l` and `-l'`; the kernel `e_{-λ}` is the conjugate of `e_λ`.
-/

namespace New.OscillatorPair

variable {R C I : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Fintype I]
  [DecidableEq I] {η : I → ℤˣ} {ε : R → ℤˣ} {ε' : C → ℤˣ} {l : HCParam ε} {l' : HCParam ε'}
  {Φ : MvPolynomial I ℂ} {T : FockDualPair (R := R) (C := C) ε ε' I}
  {π : USign ε →* Fock.fockSpace η →L[ℂ] Fock.fockSpace η}
  {π' : USign ε' →* Fock.fockSpace η →L[ℂ] Fock.fockSpace η}

open DiscreteSeries Fock Finset MeasureTheory Fintype GlModule Matrix.Norms.L2Operator

/-- Let `T` be the data of a dual pair in Fock space: a sign `T.globalSign`, integers `T.rowShift`
and `T.columnShift`, and variables indexed by `R × C`, with `R` and `C` nonempty. If `π` of `U(ε)`
and `π'` of `U(ε')` form an oscillator pair for `T` (two commuting oscillator representations on
one Fock space, `π` on the rows and `π'` on the columns), then `π'` and `π` form an oscillator pair
for `T.swap`. `T.swap` exchanges rows and columns, has sign `-T.globalSign`, row shift
`T.columnShift` and column shift `T.rowShift`. -/
theorem swap (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C] :
    OscillatorPair T.swap π' π where
  toOscillatorRep := hp.column_rep
  column_rep := by
    rw [T.swap_swap]
    exact hp.toOscillatorRep
  commute g h := (hp.commute h g).symm

/-- The operator `π(e_λ)` commutes with the action of the second group. -/
theorem map_integratedRep_dsKernel (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) (g' : USign ε') (x : fockSpace η) :
    π' g' (integratedRep π l.dsKernel x) = integratedRep π l.dsKernel (π' g' x) := by
  -- `π(e_λ)` is an integral over the first group, and `π' g'` commutes with each `π g`.
  have h_int (L : fockSpace η →L[ℂ] fockSpace η) (y : fockSpace η) :
      L (integratedRep π l.dsKernel y) = ∫ g : USign ε, l.dsKernel g • L (π g y) :=
    map_integratedRep hp.unitary_rep
      ((hΦ.hasLargeGap le_rfl).integrable_dsKernel_mul_norm_pow _ (Nat.le_succ _)) L y
  calc π' g' (integratedRep π l.dsKernel x) = ∫ g : USign ε, l.dsKernel g • π g (π' g' x) := by
        simp only [h_int, ← mul_apply_eq_comp, (hp.commute _ g').eq]
    _ = integratedRep π l.dsKernel (π' g' x) := (h_int 1 _).symm

/-- Along the map `P ↦ π(e_λ) P` from polynomials to Fock space, the representation `π'` of the
second group has the column action `T.swap.oscRows` as its derived action. -/
theorem isDerivedAction_integratedRep (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) :
    IsDerivedAction π' ((integratedRep π l.dsKernel).toLinearMap ∘ₗ polyVector η)
      T.swap.oscRows := by
  intro Y v
  -- `π(e_λ)` may be applied to the derivative of `π'` along `polyVector`.
  simpa [hp.map_integratedRep_dsKernel hΦ] using
    (hp.column_rep.derives Y v).map_clm (integratedRep π l.dsKernel)

/-- For an oscillator pair π, π' on Fock space and a joint harmonic Φ of parameters `l = 2λ` and
`l' = 2λ'`, the real part of ⟨Φ, π(e_λ)Φ⟩ is positive. Here `π(e_λ)` is the operator `∫ e_λ g • π g`
of the discrete series kernel `e_λ` (`New.HCParam.dsKernel`). -/
theorem re_inner_integratedRep_pos (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) :
    0 < (fockInner Φ (integratedRep π l.dsKernel Φ)).re := by
  -- `Φ` is highest of weight `Λ` and `⟨Φ, π z Φ⟩ > 0` for positive definite `z`
  obtain ⟨h_ne, -, h_harmonic, h_highest, -⟩ := hΦ.isJointHighest
  exact re_integratedRep_dsKernel_pos (hΦ.hasLargeGap le_rfl) hp.unitary_rep hp.derives h_highest
    fun z ↦ hp.inner_pos Φ z h_ne h_harmonic

/-- Let `Φ` be a joint harmonic (nonzero, highest of the lowest `K`-types and harmonic on both
sides) of an oscillator pair `π`, `π'` (commuting oscillator representations) and `f` a function on
the second group such that `g ↦ f g ‖g‖ ^ card I` is integrable and `f * e_λ' = e_λ'`, where `e_λ`
and `e_λ'` are the discrete series kernels of the parameters `l` and `l'`. Then the operator `π'(f)`
fixes `π(e_λ) Φ`. This applies to `f = e_λ'` and to bump functions that reproduce `e_λ'`. -/
theorem integratedRep_integratedRep_eq_self (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) {f : USign ε' → ℂ}
    (hf : Integrable fun g : USign ε' ↦ f g * ‖g.val.val‖ ^ Fintype.card I)
    (h_repro : ∀ g : USign ε', ∫ y : USign ε', f y * l'.dsKernel (y⁻¹ * g) = l'.dsKernel g) :
    integratedRep π' f (integratedRep π l.dsKernel Φ) = integratedRep π l.dsKernel Φ := by
  -- Put `proj P = π(e_λ) P`. The polynomial `Φ` is highest of weight `Λ'` for the second group, so
  -- by rigidity it suffices that `proj Φ` has the Casimir value `l'.casimirValue`. Compare the
  -- centred Casimir elements of the two groups.
  obtain ⟨-, highest', -, ⟨h_weight, -⟩, -⟩ := hΦ.isJointHighest
  let proj : MvPolynomial I ℂ →ₗ[ℂ] fockSpace η :=
    (integratedRep π l.dsKernel).toLinearMap ∘ₗ polyVector η
  have h_casimir : proj (T.oscRows.casimirK 1 Φ) = (l.casimirValue : ℂ) • proj Φ :=
    integratedRep_dsKernel_casimir (hΦ.hasLargeGap le_rfl) hp.unitary_rep hp.derives
  have h_first : proj (T.oscRows.centredCasimir T.centre Φ) =
      (∑ r, (l r / 2 - T.centre) ^ 2 - card R * (card R ^ 2 - 1) / 12 : ℂ) • proj Φ := by
    rw [centredCasimir_apply _ _ h_weight, map_add, map_sub, map_smul, map_smul, h_casimir,
      ← hΦ.hasGap_row.casimirValue_sub_centre, add_smul, sub_smul]
  have h_second : proj (T.swap.oscRows.centredCasimir T.swap.centre Φ) =
      (∑ c, (l' c / 2 - T.swap.centre) ^ 2 - card C * (card C ^ 2 - 1) / 12 : ℂ) • proj Φ := by
    rw [T.centredCasimir_swap_oscRows_eq_add, LinearMap.add_apply, map_add, h_first,
      LinearMap.smul_apply, Module.End.one_apply, map_smul, ← add_smul,
      hΦ.centred_casimirValue_eq]
  -- Restore the centre of the second group.
  have h_casimir' : proj (T.swap.oscRows.casimirK 1 Φ) = (l'.casimirValue : ℂ) • proj Φ := by
    rw [centredCasimir_apply _ _ highest'.1, map_add, map_sub, map_smul, map_smul,
      ← hΦ.hasGap_column.casimirValue_sub_centre, add_smul, sub_smul] at h_second
    exact sub_left_injective (add_right_cancel h_second)
  exact integratedRep_fix_of_isKHighest (ι := proj) (hΦ.swap.hasLargeGap le_rfl)
    hp.column_rep.unitary_rep (hp.isDerivedAction_integratedRep hΦ) hf highest' h_casimir' le_rfl
    h_repro

/-- If `Q` is highest of a weight `ν` with `ν - Λ` outside the cone of the positive roots, where `Λ`
is the lowest `K`-type of `l`, then `π(e_λ)` kills every derivative `Y Q` of `Q` along the rows. -/
theorem integratedRep_oscRows_eq_zero (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) {ν : R → ℤ} {Q : MvPolynomial I ℂ}
    (hQ : l.IsKHighest T.oscRows ν Q) (hν : ν - l.lowestKType ∉ l.rootCone) (Y : Matrix R R ℂ) :
    integratedRep π l.dsKernel (polyVector η (T.oscRows Y Q)) = 0 := by
  -- `π(e_λ)` kills the orbit of `Q`, hence also its derivatives.
  have h_unitary (Z : unitaryLie (signMatrix ε)) :
      integratedRep π l.dsKernel (polyVector η (T.oscRows Z Q)) = 0 := by
    have h_deriv : HasDerivAt
        (fun t : ℝ ↦ integratedRep π l.dsKernel (π (expU (t • Z)) (polyVector η Q))) _ 0 :=
      (hp.derives Z Q).map_clm (integratedRep π l.dsKernel)
    simp [← h_deriv.deriv, integratedRep_eq_zero_of_notMem_rootCone (hΦ.hasLargeGap le_rfl)
      hp.unitary_rep hp.derives hQ hν]
  rw [eq_unitaryLiePart_add_I_smul ε Y]
  simp [h_unitary]

/-- Let `π`, `π'` be an oscillator pair for `T`: commuting representations of `U(ε)` and `U(ε')` on
one Fock space, acting on the rows and columns. Let `R`, `C` be nonempty. Let `Φ` be a joint
harmonic: `l`, `l'` match, and `Φ ≠ 0` is `K`-highest of the lowest `K`-type weights and termwise
harmonic for `T` and `T.swap`. Then for every polynomial `P` there is a smooth compactly supported
`α` on the second group (an element of `Bumps ε'`) with `π(e_λ) P = π'(α') π(e_λ) Φ`, where
`α' g = α g⁻¹` and `e_λ` is the discrete series kernel. The inversion is the convention of
`DiscreteSeries.smear`; `α'` is again smooth with compact support.

This smoothing statement is used in place of Howe's duality theorem for real unitary pairs (R. Howe,
Transcending classical invariant theory). It is proved by Howe's argument
(`New.IsJointHarmonic.howe_argument`) instead of through irreducibility. -/
theorem exists_bump_integratedRep_eq (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) (P : MvPolynomial I ℂ) : ∃ α : Bumps ε',
    integratedRep π l.dsKernel (polyVector η P) = integratedRep π'
      (fun g : USign ε' ↦ α.val.val g⁻¹) (integratedRep π l.dsKernel Φ) := by
  -- Let `proj = π(e_λ) ∘ polyVector`, and let `smearΦ α` be `π'(g ↦ α g⁻¹)` applied to `proj Φ`.
  -- The polynomials that `proj` sends into the range of `smearΦ` satisfy the conditions of Howe's
  -- argument `IsJointHarmonic.howe_argument`, so every polynomial is among them.
  have hrep : IsUnitaryRep (Fintype.card I) π' fockInner := hp.column_rep.unitary_rep
  let proj : MvPolynomial I ℂ →ₗ[ℂ] fockSpace η :=
    (integratedRep π l.dsKernel).toLinearMap ∘ₗ polyVector η
  -- Integration by parts: `π(e_λ) = A ψ` for the generator `ψ = (-l).dsGenerator`, and
  -- `A f (Y v) = -A (Y f) v`. The generator is highest of weight `(-l).lowestKType` for `-l`.
  obtain ⟨A, hA, hA_parts⟩ :
      ∃ A : (-l).DsModule →ₗ[ℂ] fockSpace η →L[ℂ] fockSpace η,
        integratedRep π l.dsKernel = A (-l).dsGenerator ∧
        ∀ (Y : Matrix R R ℂ) (f : (-l).DsModule) (v : MvPolynomial I ℂ),
          A f (polyVector η (T.oscRows Y v)) = -A ((-l).dsAction Y f) (polyVector η v) :=
    exists_integration_by_parts (hΦ.hasLargeGap le_rfl) hp.unitary_rep hp.derives
  obtain ⟨hweight, hkill⟩ :
      (-l).IsKHighest (-l).dsAction (-l).lowestKType (-l).dsGenerator :=
    isKHighest_dsGenerator hΦ.hasGap_row.neg
  let smearΦ : Bumps ε' →ₗ[ℂ] fockSpace η :=
    .proj 1 ∘ₗ smear (fun g : USign ε' ↦ π' g (proj Φ)) (hrep.continuous (proj Φ))
  have h_smear (α : Bumps ε') :
      integratedRep π' (fun g ↦ α.val.val g⁻¹) (proj Φ) = smearΦ α := by
    simpa [smearΦ] using map_integratedRep hrep (integrable_bump_inv_smul _ α) (.id ℂ _) (proj Φ)
  suffices h_top : smearΦ.range.comap proj = ⊤ by
    obtain ⟨α, hα⟩ := h_top.ge (x := P) trivial
    exact ⟨α, hα.symm.trans (h_smear α).symm⟩
  refine hΦ.howe_argument _ ?_ ?_ ?_ ?_ ?_
  · -- Stable under the columns: if `proj y = smearΦ β`, differentiate `π'(exp tZ) (proj y)` at
    -- `t = 0` in two ways; the derivative moves onto `β` (`hasDerivAt_smear`). A general `Y` is
    -- `Z₁ + i Z₂` by `eq_unitaryLiePart_add_I_smul`.
    rintro Y y ⟨β, hβ⟩
    have hZ (Z : unitaryLie (signMatrix ε')) :
        proj (T.swap.oscRows Z y) = smearΦ (bumpDeriv (Z : Matrix C C ℂ) β) := by
      have h_orbit (g : USign ε') : π' g (proj y) =
          smear (fun x : USign ε' ↦ π' x (proj Φ)) (hrep.continuous (proj Φ)) β g := by
        simp [← hβ, ← h_smear β, map_integratedRep hrep (integrable_bump_inv_smul ..) (π' g)]
      have h_right : HasDerivAt (fun t : ℝ ↦ π' (expU (t • Z)) (proj y))
          (smearΦ (bumpDeriv Z.1 β)) 0 := by
        simpa [smearΦ, h_orbit] using
          hasDerivAt_smear _ β (hrep.continuous (proj Φ)) (hasDerivAt_expU Z 1 0)
      exact (hp.isDerivedAction_integratedRep hΦ Z y).unique h_right
    refine ⟨bumpDeriv Y β, ?_⟩
    rw [eq_unitaryLiePart_add_I_smul ε' Y]
    simp [map_add, hZ]
  · -- Contains `Φ`: a bump function that reproduces `e_{λ'}` fixes `proj Φ`.
    obtain ⟨α, hα⟩ : ∃ α : Bumps ε', ∀ g : USign ε',
        ∫ x : USign ε', α.val.val x⁻¹ * l'.dsKernel (x⁻¹ * g) = l'.dsKernel g :=
      (hΦ.swap.hasLargeGap le_rfl).exists_bump_conv_dsKernel
    have h_fix : integratedRep π' (fun g : USign ε' ↦ α.val.val g⁻¹) (proj Φ) = proj Φ :=
      hp.integratedRep_integratedRep_eq_self hΦ (integrable_bump_inv_smul _ α) hα
    exact ⟨α, (h_smear α).symm.trans h_fix⟩
  · -- If `Q` is highest of a weight outside `Λ + cone`, then `π(e_λ)` kills its derivatives.
    intro ν Q hQ hν Y
    have h_zero : proj (T.oscRows Y Q) = 0 := hp.integratedRep_oscRows_eq_zero hΦ hQ hν Y
    exact ⟨0, by simp [h_zero]⟩
  · -- By parts, the compact lowering operators of `l` move onto `ψ`, which they kill.
    intro a b hab hl P
    have h_zero : proj (T.oscRows.E b a P) = 0 := by
      simp [proj, hA, hA_parts, hkill b a hab.symm (by simpa using hl)]
    exact ⟨0, by simp [h_zero]⟩
  · -- By parts, `E a a` moves onto `ψ`, which has weight `-Λ`.
    intro a P
    have h_gap : l.HasGap _ := hΦ.hasGap_row
    have h_zero : proj (T.oscRows.E a a P - (l.lowestKType a : ℂ) • P) = 0 := by
      simp [proj, hA, hA_parts, hweight]
    exact ⟨0, by simp [h_zero]⟩

end New.OscillatorPair
