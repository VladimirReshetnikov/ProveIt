import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
import Lib.Weil.Fock.PolynomialVectors

/-!
# Harmonic matrix coefficients of the Weil representation and oscillator pairs on matrices

Let ω₀ = `New.Fock.realWeil` be the Weil representation of U(ε) on the Fock space. Let u be block
diagonal with respect to labels d, and let P, Q be harmonic: ∂_i∂_j kills them whenever d_i = d_j
and ε_i ≠ ε_j. Then the coefficient ⟨v_Q, ω₀(u) v_P⟩ is an inner product after a linear
substitution, divided by the determinant of the negative block of u. The dual pair U(ε) × U(ε′) acts
on the Fock space of R × C matrices, and the pulled-back, det-twisted Weil representations of the
two factors form an oscillator pair.

## Main definitions and results

* `New.Fock.complexLinearPart`: the matrix formed from the positive block of u and the conjugate of
  its negative block; it is invertible.
* `New.Fock.fockMatrixCoeff_eq_fockInner`: the coefficient is an inner product after a linear
  substitution (`New.linSubst`), divided by the determinant of the negative block of u.
* `New.Fock.detTwist`: the Weil representation `New.Fock.realWeil` pulled back along a homomorphism
  f and twisted by det^γ; `New.Fock.isUnitaryRep_detTwist`, `New.Fock.isDerivedAction_detTwist`,
  `New.Fock.fockInner_detTwist_pos` give unitarity with polynomial growth of the operator norm
  (`New.IsUnitaryRep`), the derivative (`New.IsDerivedAction`) and positivity at positive definite
  elements.
* `New.OscillatorRep`, `New.OscillatorPair`: these three properties as a structure, for U(ε) acting
  on the Fock space of an arbitrary dual-pair datum `T : New.FockDualPair ε ε' ι`, and for commuting
  actions of U(ε) and of U(ε′) (the latter via `T.swap`).
* `New.Fock.oscillatorPair_detTwist`: the twisted left and right actions on matrices form such a
  pair.

Notions from other files:
* `New.USign`: for a vector of signs ε, the unitary group U(ε) of the diagonal matrix diag(ε).
* `New.Fock.fockInner`: the bounded sesquilinear form (c, c′) ↦ ∫ c̄ c′ on the Fock space,
  conjugate-linear in the first variable.
* `New.Fock.polyVector`: the linear map P ↦ v_P from complex polynomials to the Fock space,
  v_P(x) = P(ζ(x))exp(−|x|²/2), where ζ(x)_i is x̄_i at positive and x_i at negative coordinates.
* `New.Fock.fockMatrixCoeff`: the coefficient ⟨v_Q, ω₀(u) v_P⟩, written `fockMatrixCoeff u Q P`.
* `New.Fock.weilDeriv`: the derivative of `New.Fock.realWeil` on polynomials, the linear map u ↦ Σ
  u_ab A_a B_b, where (A_a, B_a) is (X_a, ∂_a) if ε_a = 1 and (−∂_a, X_a) otherwise; A_a is
  `raiseOp ε a` and B_a is `lowerOp ε a`.

## Relation to the literature

Known result: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q). Here the
space is the L¹ (Feichtinger) space of vacuum coefficients rather than the Hilbert Fock space, and
weighted moments replace Schwartz seminorms. This file treats unitarity, growth, the derivative and
the coefficients between harmonic polynomials. Source: M. G. Davidson, The harmonic representation
of U(p,q) and its connection with the generalized unit disk, Pacific J. Math. 129 (1987), §1 and
Prop. 2.2; G. B. Folland, Harmonic Analysis in Phase Space (1989), ch. 1, 4; H. Reiter, Metaplectic
Groups and Segal Algebras, LNM 1382 (1989).
-/

/-!
## Matrix coefficients between harmonic polynomial vectors

The identities `New.Fock.fockMatrixCoeff_raiseOp` and `New.Fock.fockMatrixCoeff_lowerOp`, which
move `raiseOp` and `lowerOp` from one polynomial of a coefficient to the other, are solved for a
factor X_j on the left (`New.Fock.fockMatrixCoeff_X_mul`). Induction by Euler's identity
(`New.Fock.harmonic_induction`) then reduces `New.Fock.fockMatrixCoeff_eq_fockInner` to the overlap
of the vacuum with its image.
-/

namespace New.Fock

open Matrix MvPolynomial Finset Int Heisenberg.IsVacuum

variable {ι : Type _} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} (u : USign ε)

/-- For u in U(diag ε), the matrix P₊ u P₊ + P₋ ū P₋, with P₊, P₋ the projections `New.Fock.posProj`
on the positive and negative coordinates and ū the entrywise conjugate of u (written `uᴴᵀ`). -/
noncomputable def complexLinearPart : Matrix ι ι ℂ :=
  posProj ε * u * posProj ε + posProj (-ε) * (u : Matrix ι ι ℂ)ᴴᵀ * posProj (-ε)

/-- The entry of `complexLinearPart u` at (i, j) is u_ij if both signs are positive, its conjugate
if both are negative, and zero if the signs differ. -/
lemma complexLinearPart_apply (i j : ι) :
    complexLinearPart u i j =
      if ε i = ε j then
        (if ε i = 1 then (u : Matrix ι ι ℂ) i j else star ((u : Matrix ι ι ℂ) i j))
      else 0 := by
  obtain hi | hi := units_eq_one_or (ε i) <;> obtain hj | hj := units_eq_one_or (ε j) <;>
    simp [complexLinearPart, posProj, hi, hj]

/-- The determinant of `complexLinearPart u` is the conjugate of the determinant of the negative
block of u (`New.Fock.realMultiplier`) times the principal minor of u on the indices whose sign is
not −1, that is, the determinant of the positive block. -/
lemma det_complexLinearPart :
    (complexLinearPart u).det =
      realMultiplier u * principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ¬ε i = -1 := by
  have h_block (i : ι) (hi : ¬ε i = -1) (j : ι) (hj : ε j = -1) : complexLinearPart u i j = 0 := by
    simp [complexLinearPart_apply, hj, hi]
  rw [twoBlockTriangular_det _ _ h_block, realMultiplier, principalMinor, principalMinor,
    RingHom.map_det]
  congr 2 <;> ext ⟨i, hi⟩ ⟨j, hj⟩
  · simp [toSquareBlockProp, complexLinearPart_apply, hi, hj]
  · simp [toSquareBlockProp, complexLinearPart_apply, units_ne_iff_eq_neg.1 hi,
      units_ne_iff_eq_neg.1 hj]

/-- For u in U(ε), the conjugate `realMultiplier u` of the determinant of the negative block of u is
not zero. -/
lemma realMultiplier_ne_zero : realMultiplier u ≠ 0 := fun h_zero ↦ by
  -- The cocycle identity at `(u, u)` writes `1` as a product with the factor `realMultiplier u`.
  simpa [realAction, h_zero] using (realAction ε).cocycle u u

/-- The matrix `complexLinearPart u` is invertible, since both diagonal blocks of u are. -/
noncomputable instance : Invertible (complexLinearPart u) :=
  invertibleOfIsUnitDet (complexLinearPart u) <| by
    have h_pos : principalMinor (u : Matrix ι ι ℂ) (fun i : ι ↦ ¬ε i = -1) =
        (u : Matrix ι ι ℂ).det * realMultiplier u := U.principalMinor_compl u
    rw [det_complexLinearPart, h_pos]
    simp [realMultiplier_ne_zero, GeneralLinearGroup.det_ne_zero]

omit [DecidableEq ι] in
/-- Induction for polynomials P with ∂_i∂_j P = 0 whenever r(i, j). A subspace S contains all of
them if it contains 1 and contains X_j P whenever P ∈ S and ∂_i P = 0 for all i with r(i, j). -/
lemma harmonic_induction {r : Rel ι ι} (S : Submodule ℂ (MvPolynomial ι ℂ)) (h_one : 1 ∈ S)
    (h_mul : ∀ j : ι, ∀ P ∈ S, (∀ i : ι, r i j → pderiv i P = 0) → X j * P ∈ S)
    (P : MvPolynomial ι ℂ) (hP : ∀ i j : ι, r i j → pderiv i (pderiv j P) = 0) : P ∈ S := by
  have h_comm (j : ι) (m : ℕ) (R : MvPolynomial ι ℂ) :
      pderiv j (homogeneousComponent (m + 1) R) = homogeneousComponent m (pderiv j R) := by
    simp [MvPolynomial.ext_iff, coeff_pderiv, coeff_homogeneousComponent]
  -- It suffices to treat the homogeneous components, by induction on the degree. Euler's identity
  -- writes the component of degree `n + 1` through those of degree `n` of the derivatives.
  have h_comp (n : ℕ) : homogeneousComponent n P ∈ S := by
    induction n generalizing P with
    | zero => simpa [C_eq_smul_one] using S.smul_mem _ h_one
    | succ n ih =>
      have h_euler : ((n + 1 : ℕ) : ℂ) • homogeneousComponent (n + 1) P =
          ∑ j : ι, X j * homogeneousComponent n (pderiv j P) := by
        simp [← h_comm, (homogeneousComponent_mem (n + 1) P).sum_X_mul_pderiv,
          ← Nat.cast_smul_eq_nsmul ℂ]
      rw [← S.smul_mem_iff (NeZero.natCast_ne (n + 1) ℂ), h_euler]
      have h_deriv (j i k : ι) (hik : r i k) : pderiv i (pderiv k (pderiv j P)) = 0 := by
        rw [pderiv_comm k j, pderiv_comm i j, hP i k hik, map_zero]
      refine sum_mem fun j _ ↦ h_mul j _ (ih _ (h_deriv j)) fun i hij ↦ ?_
      cases n <;> simp [h_comm, hP i j hij]
  rw [← P.sum_homogeneousComponent]
  exact sum_mem fun n _ ↦ h_comp n

variable {κ : Sort*} {d : ι → κ}

/-- Let u in U(ε) be block diagonal for the labels d, and let C = `New.Fock.complexLinearPart` u be
the matrix P₊uP₊ + P₋ūP₋, where P₊, P₋ project on the coordinates with εᵢ = 1 and εᵢ = −1 and ū is
the entrywise conjugate of u. If ∂_k Q = 0 for all k with d_k = d_i and ε_k ≠ ε_i, then ⟨v_Q, ω₀(u)
v_{∂_i P}⟩ = ∑_k conj(C_ki) ⟨v_{X_k Q}, ω₀(u) v_P⟩. Here `fockMatrixCoeff u Q P` is ⟨v_Q, ω₀(u)
v_P⟩, a coefficient of the Weil representation ω₀, and v_P = `polyVector ε P` is the Fock vector of
P. -/
lemma fockMatrixCoeff_pderiv (hd : ∀ i j : ι, d i ≠ d j → (u : Matrix ι ι ℂ) i j = 0)
    (P : MvPolynomial ι ℂ) {Q : MvPolynomial ι ℂ} {i : ι}
    (hQ : ∀ k : ι, d k = d i → ε k ≠ ε i → pderiv k Q = 0) :
    fockMatrixCoeff u Q (pderiv i P) =
      ∑ k : ι, star (complexLinearPart u k i) * fockMatrixCoeff u (X k * Q) P := by
  -- In the relations between `raiseOp` and `lowerOp` the terms `k` of the other sign vanish: they
  -- are derivatives of `Q` if `d k = d i`, and otherwise the entry of `u` is zero.
  have h_other (k : ι) (hk : ε k ≠ ε i) :
      (u : Matrix ι ι ℂ) k i = 0 ∨ fockMatrixCoeff u (pderiv k Q) P = 0 := by
    by_cases h_label : d k = d i
    · simp [hQ k h_label hk]
    · simp [hd k i h_label]
  have h_raise : fockMatrixCoeff u Q (raiseOp ε i P) =
      ∑ k : ι, (u : Matrix ι ι ℂ) k i * ε k * fockMatrixCoeff u (lowerOp ε k Q) P :=
    fockMatrixCoeff_raiseOp u P Q i
  have h_lower : ε i * fockMatrixCoeff u Q (lowerOp ε i P) =
      ∑ k : ι, star ((u : Matrix ι ι ℂ) k i) * fockMatrixCoeff u (raiseOp ε k Q) P :=
    fockMatrixCoeff_lowerOp u P Q i
  obtain hi | hi := units_eq_one_or (ε i)
  · have h_left : fockMatrixCoeff u Q (pderiv i P) = ε i * fockMatrixCoeff u Q (lowerOp ε i P) := by
      simp [lowerOp, hi]
    rw [h_left, h_lower]
    refine sum_congr rfl fun k _ ↦ ?_
    obtain hk | hk := units_eq_one_or (ε k)
    · simp [complexLinearPart_apply, raiseOp, hi, hk]
    · simpa [complexLinearPart_apply, raiseOp, hi, hk] using h_other k
  · have h_left : fockMatrixCoeff u Q (pderiv i P) = -fockMatrixCoeff u Q (raiseOp ε i P) := by
      simp [raiseOp, hi]
    rw [h_left, h_raise, ← sum_neg_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    obtain hk | hk := units_eq_one_or (ε k)
    · simpa [complexLinearPart_apply, lowerOp, hi, hk] using h_other k
    · simp [complexLinearPart_apply, lowerOp, hi, hk]

/-- Let u ∈ U(diag ε) satisfy u_ij = 0 whenever d_i ≠ d_j. Let A = (`New.Fock.complexLinearPart`
u)⁻¹, where `complexLinearPart u` = P₊ u P₊ + P₋ ū P₋, with P₊ and P₋ the projections onto the
positive and negative coordinates and ū the entrywise conjugate of u. If ∂_i Q = 0 for all i with
d_i = d_j and ε_i ≠ ε_j, then ⟨v_{X_j Q}, ω₀(u) v_P⟩ = ∑_i conj(A_ij) ⟨v_Q, ω₀(u) v_{∂_i P}⟩. Here
`fockMatrixCoeff u Q P` is the Weil-representation coefficient ⟨v_Q, ω₀(u) v_P⟩, and conj(A_ij) is
written as the entry (j, i) of the inverse of the conjugate transpose. -/
lemma fockMatrixCoeff_X_mul (hd : ∀ i j : ι, d i ≠ d j → (u : Matrix ι ι ℂ) i j = 0)
    (P : MvPolynomial ι ℂ) {Q : MvPolynomial ι ℂ} {j : ι}
    (hQ : ∀ i : ι, d i = d j → ε i ≠ ε j → pderiv i Q = 0) :
    fockMatrixCoeff u (X j * Q) P =
      ∑ i : ι, (complexLinearPart u)ᴴ⁻¹ j i * fockMatrixCoeff u Q (pderiv i P) := by
  -- Solve the equations `fockMatrixCoeff_pderiv` for the indices with the label and sign of `j`.
  let w (k : ι) : ℂ := fockMatrixCoeff u (X k * Q) P
  let b (i : ι) : Prop := d i = d j ∧ ε i = ε j
  have h_row (i : ι) (hi : b i) :
      ((complexLinearPart u)ᴴ *ᵥ w) i = fockMatrixCoeff u Q (pderiv i P) := by
    obtain ⟨hi_label, hi_sign⟩ := hi
    rw [fockMatrixCoeff_pderiv u hd P fun k hk_label hk_sign ↦
      hQ k (hk_label.trans hi_label) (hk_sign.trans_eq hi_sign)]
    simp [mulVec, dotProduct, w]
  -- The indices that are not in `b` do not enter row `j` of the inverse: `(complexLinearPart u)ᴴ`
  -- is block triangular for `b`, with the order `False < True` on propositions.
  let := Prop.linearOrder
  have h_block : (complexLinearPart u)ᴴ.BlockTriangular b := fun i k hik ↦ by
    obtain ⟨⟨hi_label, hi_sign⟩, hk⟩ : b i ∧ ¬b k := by simpa [lt_iff_le_not_ge] using hik.not_ge
    by_cases h_label : d k = d i
    · have h_sign : ε k ≠ ε i := fun h_eq ↦ hk ⟨h_label.trans hi_label, h_eq.trans hi_sign⟩
      simp [complexLinearPart_apply, h_sign]
    · simp [complexLinearPart_apply, hd k i h_label]
  have h_zero (i : ι) (hi : ¬b i) : (complexLinearPart u)ᴴ⁻¹ j i = 0 :=
    blockTriangular_inv_of_blockTriangular h_block (by simp [b, lt_iff_le_not_ge, hi])
  calc w j = ((complexLinearPart u)ᴴ⁻¹ *ᵥ (complexLinearPart u)ᴴ *ᵥ w) j := by simp
    _ = ∑ i : ι, (complexLinearPart u)ᴴ⁻¹ j i * fockMatrixCoeff u Q (pderiv i P) := by
      refine sum_congr rfl fun i _ ↦ ?_
      by_cases hi : b i <;> simp [h_row, h_zero, hi]

/-- Let u in U(ε) be block diagonal for the labels d, and let P be killed by ∂_i∂_j whenever
d_i = d_j and ε_i ≠ ε_j. Then ⟨v_1, ω₀(u) v_P⟩ = (det z)⁻¹ ⟨v_1, v_P⟩. Here ω₀ is the Weil
representation, v_P = `polyVector ε P` is the Fock vector of P (v_1 is the vacuum), and z is the
negative block of u (its determinant is the `principalMinor`). -/
lemma fockMatrixCoeff_one_left (hd : ∀ i j : ι, d i ≠ d j → (u : Matrix ι ι ℂ) i j = 0)
    (P : MvPolynomial ι ℂ) (hP : ∀ i j : ι, d i = d j → ε i ≠ ε j → pderiv i (pderiv j P) = 0) :
    fockMatrixCoeff u 1 P =
      (principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1)⁻¹ *
        fockInner (polyVector ε 1) (polyVector ε P) := by
  -- Induction on `P` in the subspace of polynomials for which the identity holds.
  set c : ℂ := (principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1)⁻¹
  let S : Submodule ℂ (MvPolynomial ι ℂ) :=
    { carrier := {P | fockMatrixCoeff u 1 P = c * fockInner (polyVector ε 1) (polyVector ε P)}
      add_mem' := by simp +contextual [mul_add, add_mul]
      zero_mem' := by simp
      smul_mem' := by simp +contextual [mul_left_comm, mul_assoc] }
  -- For `P = 1` this is the overlap of the vacuum with its image.
  have h_one : 1 ∈ S := by simp [S, c, realVac, realWeil_vacVector_apply_zero]
  refine harmonic_induction (r := fun i j ↦ d i = d j ∧ ε i ≠ ε j) S h_one (fun j R _ hR ↦ ?_) P
    fun i j ⟨h_label, h_sign⟩ ↦ hP i j h_label h_sign
  -- Both sides vanish on `X j * R`. On the left move `u` across as `u⁻¹`, which is block diagonal
  -- too, and apply `fockMatrixCoeff_X_mul`.
  have hd_inv (i k : ι) (hik : d i ≠ d k) : ((u⁻¹ : USign ε) : Matrix ι ι ℂ) i k = 0 := by
    rw [U.coe_inv IsHermitianInvolution.mul_self]
    simp [signMatrix, hd k i hik.symm]
  have h_inv : fockMatrixCoeff u⁻¹ (X j * R) 1 = 0 := by
    simpa using fockMatrixCoeff_X_mul u⁻¹ hd_inv 1 fun i h_label h_sign ↦ hR i ⟨h_label, h_sign⟩
  have h_left : fockMatrixCoeff u 1 (X j * R) = star (fockMatrixCoeff u⁻¹ (X j * R) 1) := by
    rw [RCLike.star_def, conj_modelInner,
      ← modelInner_weilRep (realAction ε) u (realWeil u⁻¹ (polyVector ε 1)), rep_apply_apply]
    simp
  change fockMatrixCoeff u 1 (X j * R) = c * fockInner (polyVector ε 1) (polyVector ε (X j * R))
  rw [h_left, h_inv, ← conj_modelInner (polyVector ε (X j * R)), fockInner_X_mul]
  simp

/-- Matrix coefficients of the Weil representation ω₀ between harmonic polynomials. Let u in U(ε) be
block diagonal for the labels d, and let P, Q be killed by ∂_i∂_j whenever d_i = d_j and ε_i ≠ ε_j.
Then ⟨v_Q, ω₀(u) v_P⟩ = (det z)⁻¹ ⟨v_Q′, v_P⟩. Here v_P = `polyVector ε P` is the Fock vector of P,
z is the block of u on the coordinates with εᵢ = −1 (its determinant is the `principalMinor`), and
Q′ = `linSubst A Q` is Q after the substitution X_j ↦ Σ_i A_ij X_i, with A = C⁻¹ for
C = `New.Fock.complexLinearPart` u = P₊uP₊ + P₋ūP₋ (P₊, P₋ the projections on the positive and
negative coordinates, ū the entrywise conjugate). -/
lemma fockMatrixCoeff_eq_fockInner (hd : ∀ i j : ι, d i ≠ d j → (u : Matrix ι ι ℂ) i j = 0)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ i j : ι, d i = d j → ε i ≠ ε j → pderiv i (pderiv j Q) = 0)
    (P : MvPolynomial ι ℂ) (hP : ∀ i j : ι, d i = d j → ε i ≠ ε j → pderiv i (pderiv j P) = 0) :
    fockMatrixCoeff u Q P =
      (principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1)⁻¹ *
        fockInner (polyVector ε (linSubst (complexLinearPart u)⁻¹ Q)) (polyVector ε P) := by
  -- Induction on `Q`, for all harmonic `P` at once: both sides obey the rule
  -- `fockMatrixCoeff_X_mul`, and derivatives of harmonic polynomials are harmonic.
  set c : ℂ := (principalMinor (u : Matrix ι ι ℂ) fun i : ι ↦ ε i = -1)⁻¹
  set A : Matrix ι ι ℂ := (complexLinearPart u)⁻¹ with hA
  let S : Submodule ℂ (MvPolynomial ι ℂ) :=
    { carrier := {Q : MvPolynomial ι ℂ | ∀ P : MvPolynomial ι ℂ,
        (∀ i j : ι, d i = d j → ε i ≠ ε j → pderiv i (pderiv j P) = 0) →
        fockMatrixCoeff u Q P = c * fockInner (polyVector ε (linSubst A Q)) (polyVector ε P)}
      add_mem' := by simp +contextual [mul_add]
      zero_mem' := by simp
      smul_mem' := by simp +contextual [mul_left_comm] }
  have h_one : 1 ∈ S := fun P hP ↦ by rw [map_one, fockMatrixCoeff_one_left u hd P hP]
  refine harmonic_induction (r := fun i j ↦ d i = d j ∧ ε i ≠ ε j) S h_one
    (fun j R h_ind hR P hP ↦ ?_) Q (fun i j ⟨h_label, h_sign⟩ ↦ hQ i j h_label h_sign) P hP
  have h_deriv (i k l : ι) (h_label : d k = d l) (h_sign : ε k ≠ ε l) :
      pderiv k (pderiv l (pderiv i P)) = 0 := by
    rw [pderiv_comm l i, pderiv_comm k i, hP k l h_label h_sign, map_zero]
  have h_subst : linSubst A (X j * R) = ∑ i : ι, A i j • (X i * linSubst A R) := by
    simp [linSubst, sum_mul]
  calc fockMatrixCoeff u (X j * R) P
    _ = ∑ i : ι, star (A i j) * fockMatrixCoeff u R (pderiv i P) := by
      simp only [fockMatrixCoeff_X_mul u hd P fun i h_label h_sign ↦ hR i ⟨h_label, h_sign⟩, hA,
        ← conjTranspose_nonsing_inv, conjTranspose_apply]
    _ = ∑ i : ι, star (A i j) *
          (c * fockInner (polyVector ε (linSubst A R)) (polyVector ε (pderiv i P))) :=
      sum_congr rfl fun i _ ↦ by rw [h_ind (pderiv i P) (h_deriv i)]
    _ = c * fockInner (polyVector ε (linSubst A (X j * R))) (polyVector ε P) := by
      simp [h_subst, fockInner_X_mul, mul_sum, mul_left_comm]

end New.Fock

/-!
## Oscillator pairs on the Fock space of matrices

The dual pair U(ε) × U(ε′) acts on the Fock space `New.Fock.fockSpace` of R × C matrices, with sign
ε_r ε′_c at the entry (r, c).
-/

namespace New.Fock

open MvPolynomial Matrix ComplexOrder Kronecker MatrixOrder Fintype Norms.L2Operator
  Algebra.TensorProduct NonUnitalStarAlgHom Heisenberg.IsVacuum

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] (ε : R → ℤˣ)
  (ε' : C → ℤˣ)

/-! ### The twisted Weil representation -/

/-- The Kronecker homomorphism (not injective) from the dual pair U(ε′) × U(ε) to the unitary group
for the signs ε_r ε′_c on `R × C`: the pair `(g, h)` goes to `h ⊗ₖ g⁻¹ᵀ`, which is the action x ↦ h
x g⁻¹ on `R × C` matrices. -/
noncomputable def pairHom : USign ε' × USign ε →* USign (pairSign 1 ε ε') :=
  U.kroneckerHom IsHermitianInvolution.mul_self
    (by simp [signMatrix, pairSign, diagonal_kronecker_diagonal])

/-- The matrix of `pairHom ε ε' (g, h)` is `h ⊗ₖ g⁻¹ᵀ`. -/
lemma coe_pairHom (g : USign ε') (h : USign ε) :
    (pairHom ε ε' (g, h) : Matrix (R × C) (R × C) ℂ) =
      (h : Matrix R R ℂ) ⊗ₖ (g : Matrix C C ℂ)⁻¹ᵀ := by
  simp [pairHom]

/-- For `g` in U(ε′) and `h` in U(ε), the ℓ² operator norm of the matrix `h ⊗ₖ g⁻¹ᵀ` of
`pairHom ε ε' (g, h)` is at most `‖g‖ * ‖h‖`. -/
lemma norm_pairHom_le (g : USign ε') (h : USign ε) :
    ‖(pairHom ε ε' (g, h) : Matrix (R × C) (R × C) ℂ)‖ ≤
      ‖(g : Matrix C C ℂ)‖ * ‖(h : Matrix R R ℂ)‖ := by
  -- The matrix is `(1 ⊗ₖ g⁻¹ᵀ) * (h ⊗ₖ 1)`. Both factors are values of star algebra homomorphisms
  -- between C⋆-algebras, which do not increase the norm.
  let k : TensorProduct ℂ (Matrix R R ℂ) (Matrix C C ℂ) →⋆ₐ[ℂ] Matrix (R × C) (R × C) ℂ :=
    (kroneckerStarAlgEquiv R C ℂ).toStarAlgHom
  let left : Matrix R R ℂ →⋆ₐ[ℂ] Matrix (R × C) (R × C) ℂ := k.comp ⟨includeLeft, by simp⟩
  let right : (Matrix C C ℂ)ᵐᵒᵖ →⋆ₐ[ℂ] Matrix (R × C) (R × C) ℂ :=
    k.comp ⟨includeRight.comp (transposeAlgEquiv C ℂ ℂ).symm.toAlgHom, fun x ↦ by
      simp [star_eq_conjTranspose, conjTranspose, transpose_map]⟩
  have h_prod : (pairHom ε ε' (g, h) : Matrix (R × C) (R × C) ℂ) =
      right (.op (g⁻¹ : USign ε')) * left h := by
    change _ = (1 ⊗ₖ ((g⁻¹ : USign ε') : Matrix C C ℂ)ᵀ) * ((h : Matrix R R ℂ) ⊗ₖ 1)
    simp [← mul_kronecker_mul, coe_pairHom]
  calc _ ≤ ‖right (.op (g⁻¹ : USign ε'))‖ * ‖left h‖ := by grw [h_prod, norm_mul_le]
    _ ≤ ‖(g : Matrix C C ℂ)‖ * ‖(h : Matrix R R ℂ)‖ := by
      grw [norm_apply_le right, norm_apply_le left, MulOpposite.norm_op, U.norm_inv]

variable {ε : R → ℤˣ} {ε' : C → ℤˣ} (f : USign ε →* USign ε') (γ : ℤ)

/-- The Weil representation `realWeil` of U(ε′) on the Fock space, pulled back along a homomorphism
`f` from U(ε) to U(ε′) and twisted by `det ^ γ`: `g` acts by `det g ^ γ • realWeil (f g)`. -/
@[simps] noncomputable def detTwist : USign ε →* fockSpace ε' →L[ℂ] fockSpace ε' where
  toFun g := (g : Matrix R R ℂ).det ^ γ • realWeil (f g)
  map_one' := by simp
  map_mul' := by simp [mul_zpow, mul_comm, smul_smul]

variable {f : USign ε →* USign ε'} {γ : ℤ}

/-- For `g` in U(ε′), the operator norm of the Weil operator `realWeil g` on the Fock space is at
most the norm of the vacuum vector times the modulus of `realMultiplier g`, the conjugate of the
determinant of the negative block of `g`. -/
lemma norm_realWeil_le (g : USign ε') :
    ‖realWeil g‖ ≤ ‖(vacVector : fockSpace ε')‖ * ‖realMultiplier g‖ :=
  norm_weilRep_le (realAction ε') g

/-- Let `f` be a continuous homomorphism from U(ε) to U(ε′) with `‖f g‖ ≤ a * ‖g‖`. Then
`detTwist f γ`, the Weil representation pulled back along `f` and twisted by `det ^ γ`, is strongly
continuous, preserves the positive definite hermitian form `fockInner`, and has operator norm
`O(‖g‖ ^ card C)`. -/
lemma isUnitaryRep_detTwist {a : ℝ}
    (h_norm : ∀ {g : USign ε}, ‖(f g : Matrix C C ℂ)‖ ≤ a * ‖(g : Matrix R R ℂ)‖)
    (hf : Continuous f := by
      rw [continuous_U_iff_matrix]
      fun_prop [kroneckerMap]) :
    IsUnitaryRep (card C) (detTwist f γ) fockInner := by
  refine ⟨fun x ↦ ?_, fun g x y ↦ ?_, conj_modelInner, fun x hx ↦ ?_,
    ‖(vacVector : fockSpace ε')‖ * a ^ card C, fun g ↦ ?_⟩
  · -- Strong continuity.
    change Continuous fun g : USign ε ↦ (g : Matrix R R ℂ).det ^ γ • realWeil (f g) x
    fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])
  · -- `realWeil` preserves the form, and the determinant has modulus one.
    have h_det : (g : Matrix R R ℂ).det ^ γ * starRingEnd ℂ (g : Matrix R R ℂ).det ^ γ = 1 := by
      simp [← mul_zpow, RCLike.mul_conj]
    simp [← mul_assoc, h_det]
  · -- The form is a square norm, and it vanishes only at `0`.
    have h_ne : fockInner x x ≠ 0 := mt eq_zero_of_modelInner_self hx
    simp only [modelInner_self, Complex.ofReal_ne_zero, Complex.ofReal_re] at h_ne ⊢
    positivity
  · -- The determinant has modulus one, and the multiplier grows at most like `‖f g‖ ^ card C`.
    calc ‖detTwist f γ g‖ = ‖realWeil (f g)‖ := by simp [norm_smul]
      _ ≤ ‖(vacVector : fockSpace ε')‖ * ‖realMultiplier (f g)‖ := norm_realWeil_le (f g)
      _ ≤ ‖(vacVector : fockSpace ε')‖ * a ^ card C * ‖(g : Matrix R R ℂ)‖ ^ card C := by
        grw [mul_assoc, ← mul_pow, norm_realMultiplier_le, h_norm]

/-- Let `f` be a homomorphism from U(ε) to U(ε′) with `f (exp Y) = c • F (exp (c • Y))` for `Y` in
the Lie algebra of U(ε), where `F` is a linear map and `c` a sign. Let `ρ` be the `gl R`-module on
polynomials with action `Y ↦ weilDeriv ε' (F Y) + γ * trace Y`. Then `ρ` is the derivative of
`detTwist f γ` on the vectors `polyVector ε' P` of polynomials `P`. -/
lemma isDerivedAction_detTwist {ρ : GlModule R (MvPolynomial C ℂ)}
    (F : Matrix R R ℂ →ₗ[ℂ] Matrix C C ℂ) (c : ℤˣ)
    (hρ : ρ.ρ = weilDeriv ε' ∘ₗ F + (γ : ℂ) • (traceLinearMap R ℂ ℂ).smulRight 1)
    (h_exp : ∀ Y : unitaryLie (signMatrix ε),
      (f (expU Y) : Matrix C C ℂ) = c • F (NormedSpace.exp (c • (Y : Matrix R R ℂ)))) :
    IsDerivedAction (detTwist f γ) (polyVector ε') ρ := by
  -- Product rule for `det ^ γ` times `realWeil ∘ f` along `t ↦ expU (t • Y)`.
  intro Y P
  have h_one : expU ((0 : ℝ) • Y) = 1 := Subtype.ext (Units.ext (by simp))
  have h_det : HasDerivAt (fun t : ℝ ↦ (expU (t • Y) : Matrix R R ℂ).det) Y.val.trace 0 := by
    simpa using hasDerivAt_det_of_eq_one (by simp) (hasDerivAt_exp_smul_const Y.val (0 : ℝ))
  have h_zpow :
      HasDerivAt (fun t : ℝ ↦ (expU (t • Y) : Matrix R R ℂ).det ^ γ) (γ * Y.val.trace) 0 := by
    simpa [Function.comp_def] using (hasDerivAt_zpow γ _ (by simp)).comp 0 h_det
  -- The matrix of `f (expU (t • Y))` is `c • F (exp (t • c • Y))`, and `c * c = 1`.
  have h_f : HasDerivAt (fun t : ℝ ↦ (f (expU (t • Y)) : Matrix C C ℂ)) (F Y) 0 := by
    have h_curve : HasDerivAt (fun t : ℝ ↦ c • F (NormedSpace.exp (t • c • Y.val))) (F Y) 0 := by
      refine ((hasDerivAt_exp_smul_const (c • Y.val) 0).map_clm (.mk (c • F))).congr_deriv ?_
      simp [smul_smul]
    simpa [h_exp, smul_comm c] using h_curve
  have h_weil : HasDerivAt (fun t : ℝ ↦ realWeil (f (expU (t • Y))) (polyVector ε' P))
      (polyVector ε' (weilDeriv ε' (F Y) P)) 0 :=
    hasDerivAt_realWeil (by rw [h_one, map_one]) h_f P
  exact (h_zpow.smul h_weil).congr_deriv (by simp [hρ, smul_smul])

/-- Let π = `detTwist f γ` be the representation of U(ε) on the Fock space in which g acts by
det(g)^γ · `realWeil` (f g), the Weil representation of U(ε′) pulled back along the homomorphism `f`
and twisted by the γ-th power of the determinant. Let `z` in U(ε) and its image `f z` in U(ε′) be
positive definite, with `f z` block diagonal for labels `d` of the variables, and let `P ≠ 0` be a
polynomial killed by ∂_i∂_j whenever `i` and `j` have the same label and opposite signs. Then the
matrix coefficient ⟨v_P, π(z) v_P⟩ at the Fock vector v_P = `polyVector ε' P` is a positive real
number. -/
lemma fockInner_detTwist_pos {κ : Sort*} (d : C → κ) {P : MvPolynomial C ℂ} {z : USign ε}
    (hP_ne : P ≠ 0) (hz_pos : (z : Matrix R R ℂ).PosDef) (hfz_pos : (f z : Matrix C C ℂ).PosDef)
    (h_block : ∀ i j : C, d i ≠ d j → (f z : Matrix C C ℂ) i j = 0)
    (h_harmonic : ∀ i j : C, d i = d j → ε' i ≠ ε' j → pderiv i (pderiv j P) = 0) :
    0 < fockInner (polyVector ε' P) (detTwist f γ z (polyVector ε' P)) := by
  -- The determinant of `z` is positive and of modulus one, so the twist `det z ^ γ` is `1`.
  have h_det : (z : Matrix R R ℂ).det = 1 := by
    simpa using Complex.eq_coe_norm_of_nonneg hz_pos.det_pos.le
  suffices h_pos : 0 < fockInner (polyVector ε' P) (realWeil (f z) (polyVector ε' P)) by
    simpa [h_det] using h_pos
  -- The diagonal blocks of `f z` are positive, so `(complexLinearPart (f z))⁻¹ = b * bᴴ`.
  have h_nonneg : 0 ≤ complexLinearPart (f z) := by
    have h_proj (η : C → ℤˣ) : 0 ≤ posProj η := by simp [le_iff, posProj, apply_ite]
    exact add_nonneg (conjugate_nonneg_of_nonneg hfz_pos.posSemidef.nonneg (h_proj ε'))
      (conjugate_nonneg_of_nonneg (by simp [le_iff, hfz_pos.posSemidef]) (h_proj (-ε')))
  obtain ⟨b, hb⟩ : ∃ b : Matrix C C ℂ, (complexLinearPart (f z))⁻¹ = b * bᴴ :=
    CStarAlgebra.nonneg_iff_eq_mul_star_self.1 h_nonneg.posSemidef.inv.nonneg
  have h_subst_ne : linSubst bᴴ P ≠ 0 := fun h_zero ↦ by
    -- Substitution by `b`, then by `complexLinearPart (f z)`, undoes substitution by `bᴴ`.
    have h_undo : linSubst (complexLinearPart (f z)) (linSubst b (linSubst bᴴ P)) = P := by
      simp [← linSubst_mul, ← hb]
    simp [h_zero, hP_ne.symm] at h_undo
  -- The coefficient is the inverse determinant of the negative block of `f z` times `⟨v_Q, v_P⟩`,
  -- where `Q = linSubst (b * bᴴ) P`. Moving `b` to the other side turns the second factor into
  -- the square norm of `linSubst bᴴ P`.
  have h_coeff : fockInner (polyVector ε' P) (realWeil (f z) (polyVector ε' P)) =
      (principalMinor (f z) (ε' · = -1))⁻¹ *
        fockPairing ℂ (map (starRingEnd ℂ) (linSubst bᴴ P)) (linSubst bᴴ P) := by
    refine (fockMatrixCoeff_eq_fockInner (f z) h_block P h_harmonic P h_harmonic).trans ?_
    rw [hb, linSubst_mul, fockInner_polyVector, map_linSubst,
      show b.map (starRingEnd ℂ) = bᴴᵀ from rfl, ← fockPairing_linSubst]
  rw [h_coeff]
  exact mul_pos (inv_pos.2 (hfz_pos.submatrix Subtype.val_injective).det_pos)
    (fockPairing_star_self_pos h_subst_ne)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {η : ι → ℤˣ} (T : FockDualPair ε ε' ι)
  (π : USign ε →* fockSpace η →L[ℂ] fockSpace η)

/-! ### Oscillator pairs -/

/-- π is a strongly continuous representation of U(ε) on the Fock space with variables ι, which
preserves the form `New.Fock.fockInner` and has norm O(‖g‖ ^ |ι|). Its derivative on polynomials is
the row action `New.FockDualPair.oscRows` of the dual pair data `T` (a sign, two constants and a
bijection of R × C with ι), and ⟨v_P, π(z) v_P⟩ > 0 for z positive definite and P ≠ 0 satisfying
`New.FockDualPair.IsTermwiseHarmonic`. -/
structure _root_.New.OscillatorRep where
  /-- π is strongly continuous, preserves the positive definite hermitian form `fockInner`, and has
  norm O(‖g‖ ^ |ι|). -/
  unitary_rep : IsUnitaryRep (card ι) π fockInner
  /-- On the vectors v_P of polynomials P, the derivative of π is the action `oscRows` on the
  rows. -/
  derives : IsDerivedAction π (polyVector η) T.oscRows
  /-- ⟨v_P, π(z) v_P⟩ > 0 for z positive definite and P ≠ 0 satisfying `IsTermwiseHarmonic`: no
  monomial of P has two variables of one column from rows of opposite signs. -/
  inner_pos (P : MvPolynomial ι ℂ) (z : USign ε) (hP_ne : P ≠ 0)
    (hP_harmonic : T.IsTermwiseHarmonic P) (hz_pos : (z : Matrix R R ℂ).PosDef) :
    0 < fockInner (polyVector η P) (π z (polyVector η P))

/-- π of U(ε) and π′ of U(ε′) are commuting representations on one Fock space, each a
`New.OscillatorRep`. π acts on the rows, with the data `T`, whose sign is `T.globalSign` and whose
constant on the rows is `T.rowShift`, and π′ acts on the columns, with the data `T.swap`, whose
sign is `-T.globalSign` and whose constant on the rows is `T.columnShift`. -/
structure _root_.New.OscillatorPair (π' : USign ε' →* fockSpace η →L[ℂ] fockSpace η) extends
    OscillatorRep T π where
  /-- π' has the same properties for `T.swap`, the columns read as rows. -/
  column_rep : OscillatorRep T.swap π'
  /-- π and π' commute. -/
  commute (g : USign ε) (h : USign ε') : Commute (π g) (π' h)

/-! ### The left and right actions on matrices -/

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] {ε : R → ℤˣ}
  {ε' : C → ℤˣ}

/-- Let η be signs on the R × C matrix entries, and `weilDeriv η` the derivative of the Weil
representation on polynomials. It sends `E_ab ⊗ 1`, with `E_ab = single a b 1` a matrix unit in the
rows, to the sum over the columns `c` of the operators `glOp η (a, c) (b, c)`, that is, of the
images under `weilDeriv η` of the matrix units at ((a, c), (b, c)), so `glOp η i j` is A_i B_j. -/
lemma weilDeriv_single_kronecker_one (η : R × C → ℤˣ) (a b : R) :
    weilDeriv η (single a b 1 ⊗ₖ 1) = ∑ c : C, glOp η (a, c) (b, c) := by
  simp [weilDeriv, sum_prod_type, single_apply, ite_and, Matrix.one_apply]

/-- Let η be signs on the R × C matrix entries, and `weilDeriv η` the derivative of the Weil
representation on polynomials. It sends `1 ⊗ E_ab`, with `E_ab = single a b 1` a matrix unit in the
columns, to the sum over the rows `r` of the operators `glOp η (r, a) (r, b)`, that is, of the
images under `weilDeriv η` of the matrix units at ((r, a), (r, b)), so `glOp η i j` is A_i B_j. -/
lemma weilDeriv_one_kronecker_single (η : R × C → ℤˣ) (a b : C) :
    weilDeriv η (1 ⊗ₖ single a b 1) = ∑ r : R, glOp η (r, a) (r, b) := by
  simp [weilDeriv, sum_prod_type, single_apply, ite_and, Matrix.one_apply, mul_comm]

/-- For finite R, C with signs ε, ε′, let U(ε) act on R × C matrices by x ↦ hx (`pairHom ε ε'` at
(1, h)). On the Fock space with sign ε_r ε′_c at the entry (r, c), the representation π : h ↦ (det
h)^γ ω(x ↦ hx) (`detTwist`), with ω = `New.Fock.realWeil`, is a `New.OscillatorRep`, for the data
`New.FockDualPair.std` (sign 1, constants γ and γ′ + |R|): it is unitary, its derivative is the row
action of these data, and ⟨v_P, π(z) v_P⟩ > 0 for positive definite z and nonzero P satisfying
`IsTermwiseHarmonic`. -/
lemma oscillatorRep_detTwist_inr (γ γ' : ℤ) :
    OscillatorRep (FockDualPair.std ε ε' γ γ')
      (detTwist ((pairHom ε ε').comp (MonoidHom.inr (USign ε') (USign ε))) γ) := by
  refine ⟨isUnitaryRep_detTwist fun {z} ↦ norm_pairHom_le ε ε' 1 z, ?_,
    fun P z hP_ne hP hz_pos ↦ ?_⟩
  · -- `Y` acts by `Y ⊗ 1`; compare the two actions on the matrix units.
    refine isDerivedAction_detTwist (kroneckerBilinear.flip 1) 1
      (ext_linearMap ℂ fun a b ↦ LinearMap.ext_ring ?_) fun Y ↦ ?_
    · suffices h_unit : (FockDualPair.std ε ε' γ γ').oscRows.E a b =
          weilDeriv (pairSign 1 ε ε') (single a b 1 ⊗ₖ 1) +
            (γ : ℂ) • (single a b (1 : ℂ)).trace • 1 by
        simpa [GlModule.E, kroneckerBilinear] using h_unit
      rw [weilDeriv_single_kronecker_one]
      refine LinearMap.ext fun Q ↦ ?_
      obtain rfl | h_ne := eq_or_ne a b <;>
        simp [oscRows, oscRowsUnit, GlModule.E, smul_eq_C_mul, *]
    · simp [coe_pairHom, kroneckerBilinear]
  · -- `z ⊗ 1` is positive definite and keeps the columns.
    refine fockInner_detTwist_pos Prod.snd hP_ne hz_pos ?_ (fun i j hij ↦ ?_) ?_
    · simpa [coe_pairHom] using hz_pos.kronecker (PosDef.one (n := C))
    · simp [coe_pairHom, one_apply_ne hij]
    · rintro ⟨a, c⟩ ⟨b, -⟩ rfl h_sign
      exact hP a b c (by simpa [pairSign] using h_sign)

/-- For finite R, C with signs ε, ε′, let U(ε′) act on R × C matrices by x ↦ xg⁻¹ (`pairHom ε ε'` at
(g, 1)). On the Fock space with sign ε_r ε′_c at the entry (r, c), the representation
π : g ↦ (det g)^γ′ ω(x ↦ xg⁻¹) (`detTwist`), with ω = `New.Fock.realWeil`, is a `New.OscillatorRep`
for the data `New.FockDualPair.std` with rows and columns exchanged by `swap`: it is unitary, its
derivative is the column action with constant γ′ + |R|, and ⟨v_P, π(z) v_P⟩ > 0 for positive
definite z and nonzero P satisfying `IsTermwiseHarmonic` for the exchanged data. -/
lemma oscillatorRep_detTwist_inl (γ γ' : ℤ) :
    OscillatorRep (FockDualPair.std ε ε' γ γ').swap
      (detTwist ((pairHom ε ε').comp (MonoidHom.inl (USign ε') (USign ε))) γ') := by
  refine ⟨isUnitaryRep_detTwist fun {z} ↦ (norm_pairHom_le ε ε' z 1).trans_eq (mul_comm _ _), ?_,
    fun P z hP_ne hP hz_pos ↦ ?_⟩
  · -- `Y` acts by `-(1 ⊗ Yᵀ)`; compare the two actions on the matrix units.
    refine isDerivedAction_detTwist
      (-kroneckerBilinear 1 ∘ₗ (transposeLinearEquiv C C ℂ ℂ).toLinearMap) (-1)
      (ext_linearMap ℂ fun a b ↦ LinearMap.ext_ring ?_) fun Y ↦ ?_
    · suffices h_unit : (FockDualPair.std ε ε' γ γ').swap.oscRows.E a b =
          -weilDeriv (pairSign 1 ε ε') (1 ⊗ₖ single b a 1) +
            (γ' : ℂ) • (single a b (1 : ℂ)).trace • 1 by
        simpa [GlModule.E, kroneckerBilinear] using h_unit
      rw [weilDeriv_one_kronecker_single, swap_oscRows_E]
      -- The commutation relations `canonical_commutation` shift `γ'` by `card R`.
      refine LinearMap.ext fun Q ↦ ?_
      obtain rfl | h_ne := eq_or_ne a b <;>
        simp [glOp, add_comm, smul_eq_C_mul, Finset.sum_add_distrib,
          canonical_commutation, *]
    · simp [coe_pairHom, exp_neg, kroneckerBilinear]
  · -- `1 ⊗ z⁻¹ᵀ` is positive definite and keeps the rows.
    refine fockInner_detTwist_pos Prod.fst hP_ne hz_pos ?_ (fun i j hij ↦ ?_) ?_
    · simpa [coe_pairHom] using (PosDef.one (n := R)).kronecker hz_pos.inv.transpose
    · simp [coe_pairHom, one_apply_ne hij]
    · rintro ⟨r, a⟩ ⟨-, b⟩ rfl h_sign
      exact hP a b r (by simpa [pairSign] using h_sign)

/-- For finite R, C with signs ε, ε′, consider the Fock space of R × C matrices, with sign ε_r ε′_c
at the entry (r, c). The representations h ↦ (det h)^γ ω(x ↦ hx) of U(ε) and g ↦ (det g)^γ′
ω(x ↦ xg⁻¹) of U(ε′) (`detTwist` along `pairHom ε ε'`), with ω = `New.Fock.realWeil`, form a
`New.OscillatorPair`. That is, they commute, and each is a `New.OscillatorRep`: the first for the
data below, the second for their `swap` (rows and columns exchanged). The data are
`New.FockDualPair.std` (sign 1, constants γ and γ′ + |R|). For this data E_ab acts on the rows by
∑_c raiseOp(a,c) lowerOp(b,c) + γ δ_ab and on the columns by −∑_r raiseOp(r,b) lowerOp(r,a) + γ′
δ_ab. -/
lemma oscillatorPair_detTwist {γ γ' : ℤ} :
    OscillatorPair (FockDualPair.std ε ε' γ γ')
      (detTwist ((pairHom ε ε').comp (MonoidHom.inr (USign ε') (USign ε))) γ)
      (detTwist ((pairHom ε ε').comp (MonoidHom.inl (USign ε') (USign ε))) γ') := by
  refine ⟨oscillatorRep_detTwist_inr γ γ', oscillatorRep_detTwist_inl γ γ', fun h g ↦ ?_⟩
  have h_comm : ((1, h) : USign ε' × USign ε) * (g, 1) = (g, 1) * (1, h) := by simp
  simp [commute_iff_eq, mul_comm, ← map_mul, smul_smul, h_comm]

/-- Let R, C be finite and g a complex R × R matrix. The `principalMinor` (determinant of the
principal submatrix) of `g ⊗ₖ 1` on the indices in R × C satisfying `p` is the product over the
columns `c` of the principal minors of `g` on the rows `r` with `p (r, c)`. -/
lemma principalMinor_kronecker_one (g : Matrix R R ℂ) (p : R × C → Prop) [DecidablePred p] :
    principalMinor (g ⊗ₖ 1) p = ∏ c : C, principalMinor g fun r : R ↦ p (r, c) := by
  -- `g ⊗ₖ 1` is block diagonal with all blocks equal to `g`; swap the two indices.
  rw [kronecker_one, ← principalMinor_submatrix (Equiv.prodComm C R)]
  exact principalMinor_blockDiagonal _ _

end New.Fock
