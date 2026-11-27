import New.UpperBound.ElementaryDivisors.RootLemma

/-!
# The substitution by Frobenius powers of generic matrices; weight and defect

Fix a Frobenius cycle `T` (`New.FrobeniusCycle`; letters `s : ZMod N`, even or odd, `P` a power of
the prime `p`, `q = P ^ N`, `w ^ 2 = p`). The twists `T.embedding s g` are not algebraic in `g`, but
modulo `p` they are entrywise powers of one another. So we take one generic `k × k` matrix for each
letter (a copy) and let the copy `s - d`, `0 ≤ d ≤ ℓ`, act on the letter `s` through its entrywise
power `P ^ d`, or through the cofactor matrix of this power if `s` is odd; the last factor, `d = ℓ`,
acts on the deep variables only. The matrix of this substitution on forms is
`New.FrobeniusCycle.substitutionOperator` at the factors `New.FrobeniusCycle.frobGenericMatrix`.
Matrices act on vectors of coefficients, so they are the transposes of the matrices that are
substituted in the variables: the row index of an entry here is its column index there.

* `New.FrobeniusCycle.substitutionOperator_map_eq_conj`: conjugation of the factors by a block
  diagonal matrix.
* `New.FrobeniusCycle.copyWeight`: the weight of a monomial in the entries of all copies.
* `New.FrobeniusCycle.abs_defect_sub_copyWeight_le`: let `a' = a + 1`, `ℓ ≤ N` and
  `N n k (ℓ + 2) ≤ P ^ ℓ`, and take an entry in row `β` of the operator with `r = a'` at the factors
  `New.FrobeniusCycle.conjFrobGenericMatrix h` (the generic factors after a change of frame by `h`).
  If the coefficient of a monomial in it is not divisible by `w ^ c`, the weight of the monomial at
  the copy `i` is within `c* = 3 k c` of the defect of `β` at the letter `i + ℓ`.

A term of an entry of a product of matrices belongs to a path of indices. The weight of a step is a
difference of two scaled index weights (`New.FrobeniusCycle.scaledIndexWeight`) up to `1 / P ^ ℓ`,
so the weights telescope along a path and leave the scaled index weight of its last index, up to
`(ℓ + 2) / P ^ ℓ`. For an even letter this scaled index weight is `1 - 1 / q` times the defect
weight. For an odd letter the cofactor matrix changes its sign, which again gives this multiple of
the defect weight, and multiplies the loss by at most `k`. What remains, the defect divided by `q`,
has size at most `1`, as `2 n ≤ q`. `New.FrobeniusCycle.substitutionOperator_mem` carries this out
for all terms at once. An element has level `t` in a filtration `G` (`New.IsRealFiltration`) if it
lies in `G t`, and the levels of the entries are bounded from the levels of the factors. The main
filtrations used are `New.gaussFiltration (New.adicFiltration w) ω`: divisibility of coefficients by
powers of `w`, shifted by weights `ω` of the variables. They also absorb the error terms, which are
multiples of `p` (`New.FrobeniusCycle.conjFrobGenericMatrix_mem_gaussFiltration`). With `0` in place
of `w` the level bounds the weights of the monomials that occur.

Notions from other files:
* `New.FrobeniusCycle.deepIndicator`: the indicator of the deep variables `(b, s)`: it is `1` if `s`
  is even and `r ≤ b`, or `s` is odd and `b < r`, and `0` otherwise.
* `New.FrobeniusCycle.defectWeight i a a'`: the weight of `(b, s)` is
  `± P ^ ((s - i) mod N) / (q - 1)` for `b = a, a'` (with the sign `+` at `a'` for even and at `a`
  for odd `s`, and `1` added to the positive weight at `s = i`), and `0` for other `b`. The defect
  of a monomial at the letter `i` is the sum of these weights over its variables.
* `New.exponentOf`: a family `β` of exponent vectors, one for each letter, as one exponent vector on
  the variables `(b, s)`.
* `New.levi W (New.twoBlock k r)`: the block diagonal matrices in `GL_k(W)` with blocks of sizes `r`
  and `k - r`.

## Notation

Here `h` is a matrix in `GL_k(W)`, not a form.
-/

noncomputable section

namespace New.FrobeniusCycle

open MvPolynomial Matrix Finsupp SetLike IsRealFiltration Ideal.Quotient Fintype Function List Nat

variable {N k : ℕ} {W O R : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  [CommRing R] (T : FrobeniusCycle N W O)

/-! ### The substitution and the weights -/

/-- The generic matrix of the copy `s - d`, whose entries are the variables `X (s - d, b, c)`, with
its entries raised to the power `P ^ d`. -/
abbrev frobGenericMatrix (s : ZMod N) (d : ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (ZMod N × Fin k × Fin k) O) :=
  of fun b c : Fin k ↦ X (s - d, b, c) ^ T.P ^ d

/-- The matrix `M` if the letter `s` is even, and the transposed adjugate of `M` if `s` is odd. -/
def parityCofactor (s : ZMod N) (M : Matrix (Fin k) (Fin k) R) : Matrix (Fin k) (Fin k) R :=
  if T.isEven s then M else M.adjugateᵀ

/-- The matrix of the letter `s` in `substitutionOperator`. Its row `b` is row `b` of
`T.parityCofactor s` of the product `ψ s (m - 1) * ⋯ * ψ s 0`, where `m = ℓ + 1` if the variable
`(b, s)` is deep (`T.deepIndicator r (b, s) = 1`) and `m = ℓ` if not. -/
def substitutionLetterMatrix (r ℓ : ℕ) (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R) (s : ZMod N) :
    Matrix (Fin k) (Fin k) R :=
  of fun b c : Fin k ↦
    T.parityCofactor s ((range (ℓ + T.deepIndicator r (b, s))).map (ψ s)).reverse.prod b c

/-- The Kronecker product over the letters `s` of the `n`-th symmetric powers of the matrices
`T.substitutionLetterMatrix r ℓ ψ s`. In use the factors `ψ s d` are the entrywise powers `P ^ d` of
the copies `s - d` (`frobGenericMatrix`), or these after a change of frame
(`conjFrobGenericMatrix`). -/
def substitutionOperator (r ℓ n : ℕ) (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R) :
    Matrix (Exponents N k n) (Exponents N k n) R :=
  kroneckerPi fun s : ZMod N ↦ symPowMatrix n (T.substitutionLetterMatrix r ℓ ψ s)

/-- Conjugation `M ↦ ι(h) M ι(h)⁻¹` by the image of `h` under `ι = T.embedding s`. -/
def letterConj (h : GL (Fin k) W) (s : ZMod N) :
    Matrix (Fin k) (Fin k) O →* Matrix (Fin k) (Fin k) O where
  toFun M := h.val.map (T.embedding s) * M * h⁻¹.val.map (T.embedding s)
  map_one' := by simp
  map_mul' := by simp [mul_assoc, ← (h.val⁻¹.map _).mul_assoc]

/-- The integer vector `ρ = e_{a'} - e_a`: its entry at `a'` is `1`, at `a` it is `-1`, and the
other entries are `0` (for `a ≠ a'`). For `a' = a + 1` it is minus the simple root
`e_a - e_{a + 1}` of `GL_k`. -/
def _root_.New.rootVector (a a' b : Fin k) : ℤ :=
  (if b = a' then 1 else 0) - if b = a then 1 else 0

/-- The weight of the index `b`: the entry at `b` of `ρ = New.rootVector a a'`, divided by
`P ^ ℓ`. -/
def indexWeight (ℓ : ℕ) (a a' b : Fin k) : ℝ :=
  rootVector a a' b / (T.P ^ ℓ : ℝ)

/-- The weight at the copy `i` of a monomial `ν` in the entries of all the generic matrices. For a
monomial in one matrix let `row` and `col` be the sums of the entries of
`ρ = New.rootVector a a'` over its row indices and over its column indices. The weight is
`P ^ (-ℓ)` times the sum of `row` at the copy `i` and of `P ^ (-u) (row - col)` at the copies
`i - u`, `0 < u < N`. -/
def copyWeight (ℓ : ℕ) (a a' : Fin k) (i : ZMod N) (ν : ZMod N × Fin k × Fin k →₀ ℕ) : ℝ :=
  ((weight (fun v : Fin k × Fin k ↦ rootVector a a' v.1) (ν.curry i) : ℤ) +
    ∑ j ∈ Finset.univ.erase i, (T.P ^ (j - i).val / T.q : ℝ) *
      ((weight (fun v : Fin k × Fin k ↦ rootVector a a' v.1) (ν.curry j) : ℤ) -
        (weight (fun v : Fin k × Fin k ↦ rootVector a a' v.2) (ν.curry j) : ℤ))) / T.P ^ ℓ

/-- The scaled index weight of the index `b` at the exponent `m`: its weight
`New.FrobeniusCycle.indexWeight` times `P ^ m / q`. -/
def scaledIndexWeight (ℓ : ℕ) (a a' : Fin k) (m : ℕ) (b : Fin k) : ℝ :=
  T.indexWeight ℓ a a' b * (T.P ^ m / T.q)

/-- The weight at the copy `i` of the entry `(b, c)` of the generic matrix of the copy `j`: the
weight of the row `b` if `j = i`, and else the difference of the scaled index weights of `b` and `c`
at the exponent `(j - i) mod N`. -/
def entryWeight (ℓ : ℕ) (a a' : Fin k) (i : ZMod N) (v : ZMod N × Fin k × Fin k) : ℝ :=
  if v.1 = i then T.indexWeight ℓ a a' v.2.1
  else T.scaledIndexWeight ℓ a a' (v.1 - i).val v.2.1 - T.scaledIndexWeight ℓ a a' (v.1 - i).val
    v.2.2

/-- The adjugate commutes with conjugation: if `A B = 1`, then `B adj(A M B) A = adj(M)`. -/
lemma _root_.New.mul_adjugate_conj_mul {A B : Matrix (Fin k) (Fin k) R} (hAB : A * B = 1)
    (M : Matrix (Fin k) (Fin k) R) : B * (A * M * B).adjugate * A = M.adjugate :=
  calc B * (A * M * B).adjugate * A
      = B * B.adjugate * M.adjugate * (A.adjugate * A) := by
        simp only [adjugate_mul_distrib, mul_assoc]
    _ = M.adjugate := by simp [mul_adjugate, adjugate_mul, smul_smul, ← det_mul, hAB]

section

omit [NeZero N]

variable {h : GL (Fin k) W} {s : ZMod N} {r : ℕ}

/-- Let `T` be a Frobenius cycle, with ring maps `ι = T.embedding s : W → O` for the letters
`s : ZMod N`, each even or odd, and let `h` be in `GL_k(W)`. For even `s`, `T.parityCofactor s M`
is `M` and `T.letterMatrix s h` is `ι(h)`; for odd `s` they are the transposed adjugate of `M` and
the inverse transpose of `ι(h)`. Conjugation by `T.letterMatrix s h` undoes the conjugation
`T.letterConj h s M = ι(h) M ι(h)⁻¹` inside `T.parityCofactor s`. -/
lemma letterMatrix_mul_parityCofactor_letterConj_mul (M : Matrix (Fin k) (Fin k) O) :
    T.letterMatrix s h⁻¹ * T.parityCofactor s (T.letterConj h s M) * T.letterMatrix s h =
      T.parityCofactor s M := by
  let A : Matrix (Fin k) (Fin k) O := h.val.map (T.embedding s)
  let B : Matrix (Fin k) (Fin k) O := h⁻¹.val.map (T.embedding s)
  have hAB : A * B = 1 := by simp [A, B, ← Matrix.map_mul]
  rw [show T.letterConj h s M = A * M * B from rfl, parityCofactor, parityCofactor,
    letterMatrix_apply, letterMatrix_apply, inv_inv]
  split_ifs
  · calc B * (A * M * B) * A = B * A * M * (B * A) := by simp only [mul_assoc]
      _ = M := by rw [mul_eq_one_comm.1 hAB, one_mul, mul_one]
  · calc Aᵀ * (A * M * B).adjugateᵀ * Bᵀ = (B * (A * M * B).adjugate * A)ᵀ := by
          simp only [transpose_mul, mul_assoc]
      _ = M.adjugateᵀ := by rw [mul_adjugate_conj_mul hAB]

/-- The map `T.parityCofactor s` commutes with applying a ring map to all entries. -/
lemma parityCofactor_map (χ : R →+* O) (M : Matrix (Fin k) (Fin k) R) :
    (T.parityCofactor s M).map χ = T.parityCofactor s (M.map χ) := by
  unfold parityCofactor
  split_ifs
  exacts [rfl, congrArg Matrix.transpose (χ.map_adjugate M)]

/-- If `h` is block diagonal with blocks cut at `r`, then `T.letterMatrix s h⁻¹` mixes row `b` only
with the rows `x` for which `(x, s)` has the same depth `T.deepIndicator r` as `(b, s)`. -/
lemma letterMatrix_inv_apply_eq_zero (h_levi : h ∈ levi W (twoBlock k r)) {b x : Fin k}
    (h_depth : T.deepIndicator r (b, s) ≠ T.deepIndicator r (x, s)) :
    T.letterMatrix s h⁻¹ b x = 0 := by
  have h_ne : twoBlock k r b ≠ twoBlock k r x := by grind [deepIndicator, twoBlock]
  rw [letterMatrix_apply]
  split_ifs
  · rw [map_apply, show h⁻¹.val b x = 0 from inv_mem h_levi b x h_ne, map_zero]
  · simp [show h.val x b = 0 from h_levi x b h_ne.symm]

end

section

variable {h : GL (Fin k) W} {r ℓ n : ℕ} {ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R}

omit [NeZero N] in
/-- Let `T` be a Frobenius cycle, with ring maps `ι = T.embedding s : W → O` for the letters `s`,
and let `h` in `GL_k(W)` be block diagonal with blocks of sizes `r` and `k - r`. Row `b` of
`T.substitutionLetterMatrix r ℓ ψ s` is row `b` of `ψ s (m - 1) * ⋯ * ψ s 0` for even `s`, and of
its transposed adjugate for odd `s`, where `m = ℓ + T.deepIndicator r (b, s)` is `ℓ` on one block
and `ℓ + 1` on the other. Apply a ring map `χ` to all entries. If `S` is this matrix and `S'` the
one formed from the factors `ι(h) (ψ s d) ι(h)⁻¹` (`T.letterConj`), then `S = H⁻¹ S' H`, where
`H = T.letterMatrix s h` is `ι(h)` for even `s` and its inverse transpose for odd `s`. -/
lemma substitutionLetterMatrix_map (χ : R →+* O) (h_levi : h ∈ levi W (twoBlock k r)) (s : ZMod N) :
    (T.substitutionLetterMatrix r ℓ ψ s).map χ =
      T.letterMatrix s h⁻¹ *
        T.substitutionLetterMatrix r ℓ
          (fun (t : ZMod N) (d : ℕ) ↦ T.letterConj h t ((ψ t d).map χ)) s *
        T.letterMatrix s h := by
  -- The length of the product in row `b` depends only on `T.deepIndicator r (b, s)`, and
  -- `T.letterMatrix s h⁻¹` mixes only rows with the same value of it.
  have h_prod (m : ℕ) : (T.parityCofactor s ((range m).map (ψ s)).reverse.prod).map χ =
      T.letterMatrix s h⁻¹ *
        T.parityCofactor s
          ((range m).map fun d : ℕ ↦ T.letterConj h s ((ψ s d).map χ)).reverse.prod *
        T.letterMatrix s h := by
    rw [parityCofactor_map, ← RingHom.mapMatrix_apply,
      ← letterMatrix_mul_parityCofactor_letterConj_mul (h := h)]
    simp only [map_list_prod, List.map_reverse, List.map_map, comp_def, RingHom.mapMatrix_apply]
  have h_row (ψ' : ZMod N → ℕ → Matrix (Fin k) (Fin k) O) (b y : Fin k) :
      (T.letterMatrix s h⁻¹ * T.substitutionLetterMatrix r ℓ ψ' s) b y =
        (T.letterMatrix s h⁻¹ * T.parityCofactor s
          ((range (ℓ + T.deepIndicator r (b, s))).map (ψ' s)).reverse.prod) b y := by
    simp only [Matrix.mul_apply, substitutionLetterMatrix, of_apply]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h_depth : T.deepIndicator r (b, s) = T.deepIndicator r (x, s)
    · rw [h_depth]
    · simp [T.letterMatrix_inv_apply_eq_zero h_levi h_depth]
  ext b c
  rw [map_apply, substitutionLetterMatrix, of_apply, ← map_apply (f := χ), h_prod]
  simp only [Matrix.mul_apply (M := _ * _), h_row]

/-- Apply a ring map `χ` to all entries, and let `h` be block diagonal with blocks cut at `r`.
Conjugating each factor `ψ s d` by `h` through `T.embedding s` conjugates `T.substitutionOperator`
by `T.letterRep n h`, the matrix of `h` on forms of degree `n` in each letter. -/
lemma substitutionOperator_map_eq_conj (χ : R →+* O) (h_levi : h ∈ levi W (twoBlock k r)) :
    (T.substitutionOperator r ℓ n ψ).map χ =
      T.letterRep n h⁻¹ *
        T.substitutionOperator r ℓ n (fun (s : ZMod N) (d : ℕ) ↦ T.letterConj h s ((ψ s d).map χ)) *
        T.letterRep n h := by
  simp_rw [letterRep_apply, substitutionOperator, ← kroneckerPi_mul, ← map_mul, ← kroneckerPi_map,
    ← symPowMatrix_map, T.substitutionLetterMatrix_map χ h_levi]

/-- Applying a ring map to the Frobenius cycle does not change the operator, which uses only the
parities of the letters. -/
lemma substitutionOperator_frobeniusCycle_map {O' : Type} [CommRing O'] (χ : O →+* O') :
    (T.map χ).substitutionOperator r ℓ n ψ = T.substitutionOperator r ℓ n ψ :=
  rfl

/-- If all factors `ψ s d` are the identity matrix, then the substitution operator
`T.substitutionOperator r ℓ n ψ` is the identity matrix. -/
lemma substitutionOperator_one :
    T.substitutionOperator r ℓ n (fun (_ : ZMod N) (_ : ℕ) ↦ (1 : Matrix (Fin k) (Fin k) R)) =
      1 := by
  have h_letter (s : ZMod N) :
      T.substitutionLetterMatrix (k := k) (R := R) r ℓ (fun _ _ ↦ 1) s = 1 :=
    Matrix.ext fun b c ↦ by simp [substitutionLetterMatrix, parityCofactor]
  simp [substitutionOperator, h_letter]

end

/-! ### Levels of the entries in a filtration -/

section

variable {h : GL (Fin k) W} {s : ZMod N} {r ℓ n d : ℕ} {a a' : Fin k}
  {ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R}

/-- Let each entry of row `b` of `M` lie in `G (x b - v)` for the filtration `G`, where `v ≥ 0` and
the `x b` add up to `0`. Then each entry of row `b` of the transposed adjugate `M.adjugateᵀ` (the
cofactor matrix) lies in `G (-x b - k * v)`. -/
lemma _root_.New.adjugate_transpose_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {M : Matrix (Fin k) (Fin k) R} {x : Fin k → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hx_sum : ∑ b : Fin k, x b = 0) (hM : ∀ b c : Fin k, M b c ∈ G (x b - v)) (b c : Fin k) :
    M.adjugateᵀ b c ∈ G (-x b - k * v) := by
  -- A cofactor in row `b` is a sum of products of entries of the other rows.
  let level : Fin k → ℝ := update (fun i : Fin k ↦ x i - v) b 0
  have h_entry (i j : Fin k) : M.updateRow b (Pi.single c 1) i j ∈ G (level i) := by
    obtain rfl | hi := eq_or_ne i b
    · simp only [updateRow_self, Pi.single_apply, level, Function.update_self]
      split_ifs
      exacts [one_mem_graded G, zero_mem _]
    · simpa [level, hi] using hM i j
  have h_sum : ∑ i : Fin k, level i = -x b - k * v + v := by
    simp [level, Finset.sum_update_of_mem, Finset.sum_sub_distrib, hx_sum, Finset.card_sdiff,
      cast_pred b.pos]
    ring
  rw [transpose_apply, adjugate_apply, ← det_transpose, det_apply]
  exact sum_mem fun π _ ↦ zsmul_mem
    (antitone (by linarith) (prod_mem_graded G level _ fun i _ ↦ h_entry i (π i))) _

/-- Let the entries of row `b` of `M` have level `y b` in the filtration `G`. Rows and columns of
the `n`-th symmetric power of `M` are indexed by exponent vectors of degree `n`, and row `β` has
level `∑ b, β b * y b`. -/
lemma _root_.New.symPowMatrix_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {M : Matrix (Fin k) (Fin k) R} {y : Fin k → ℝ} (hM : ∀ b c : Fin k, M b c ∈ G (y b))
    (β γ : Monomials (Fin k) n) : symPowMatrix n M β γ ∈ G (weight y β.val) := by
  -- Give the variable `b` the weight `-y b`. The image of each variable has Gauss level `0`, hence
  -- so has the image of each monomial.
  have h_var (c : Fin k) : ∑ b : Fin k, M b c • X b ∈ gaussFiltration G (-y) 0 := by
    refine sum_mem fun b _ ↦ ?_
    rw [X, smul_monomial, smul_eq_mul, mul_one]
    exact monomial_mem_gaussFiltration (by simpa [weight_single] using hM b c)
  have h_monomial : linSubst M (monomial γ.val 1) ∈ gaussFiltration G (-y) 0 := by
    simpa [linSubst, bind₁_monomial] using
      prod_pow_mem_graded (gaussFiltration G (-y)) 0 _ γ.val fun c _ ↦ h_var c
  change (linSubst M (monomial γ.val 1)).coeff β.val ∈ G (weight y β.val)
  simpa [weight_eq_sum] using h_monomial β.val

/-- Filtration levels add up along a product. Suppose that for `d < m` each entry `(b, c)` of `A d`
lies in `G (α (d + 1) b - α d c - u)` for the filtration `G`, and that `α 0 b ≤ u` for all `b`. Then
each entry of row `b` of `A (m - 1) * ⋯ * A 0` lies in `G (α m b - (m + 1) * u)`. -/
lemma _root_.New.reverse_prod_map_range_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {A : ℕ → Matrix (Fin k) (Fin k) R} {α : ℕ → Fin k → ℝ} {u : ℝ} {m : ℕ}
    (hα_zero : ∀ b : Fin k, α 0 b ≤ u)
    (hA : ∀ d < m, ∀ b c : Fin k, A d b c ∈ G (α (d + 1) b - α d c - u)) (b c : Fin k) :
    ((range m).map A).reverse.prod b c ∈ G (α m b - (m + 1) * u) := by
  induction m generalizing b with
  | zero =>
    simp only [range_zero, List.map_nil, List.reverse_nil, List.prod_nil, Matrix.one_apply]
    split_ifs
    exacts [antitone (by simpa using hα_zero b) (one_mem_graded G), zero_mem _]
  | succ m ih =>
    simp only [range_succ, List.map_append, List.reverse_append, List.prod_append,
      List.map_singleton, List.reverse_singleton, List.prod_singleton, Matrix.mul_apply]
    refine sum_mem fun y _ ↦ ?_
    rw [show α (m + 1) b - ((m + 1 : ℕ) + 1) * u =
      α (m + 1) b - α m y - u + (α m y - (m + 1) * u) by grind]
    exact mul_mem_graded (hA m m.lt_succ_self b y) (ih (fun d hd ↦ hA d (lt_succ_of_lt hd)) y)

omit [NeZero N] in
/-- Let the entries of row `b` of the `k × k` matrix `M` have level `x b - v` in the filtration `G`
(that is, lie in `G (x b - v)`), where `v ≥ 0` and the `x b` add up to `0`. The matrix
`T.parityCofactor s M` is `M` for an even letter `s` and the transposed adjugate of `M` for an odd
one. Its row `b` has level `± x b - k v`, with the sign `+` for even and `-` for odd `s`. -/
lemma parityCofactor_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {M : Matrix (Fin k) (Fin k) R} {x : Fin k → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hx_sum : ∑ b : Fin k, x b = 0) (hM : ∀ b c : Fin k, M b c ∈ G (x b - v)) (b c : Fin k) :
    T.parityCofactor s M b c ∈ G ((if T.isEven s then 1 else -1) * x b - k * v) := by
  unfold parityCofactor
  split_ifs
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast b.pos
    exact antitone (by nlinarith) (hM b c)
  · simpa only [neg_one_mul] using adjugate_transpose_mem G hv hx_sum hM b c

/-- Let `T` be a Frobenius cycle, whose letters `s : ZMod N` are even or odd (`T.isEven`). The
variable `(b, s)` is deep (`T.deepIndicator r (b, s) = 1`, else `0`) if `r ≤ b` for even and `b < r`
for odd `s`. The matrix `T.substitutionOperator r ℓ n ψ` is the Kronecker product over `s` of the
`n`-th symmetric powers of the matrices whose row `b` is that of `ψ s (m - 1) * ⋯ * ψ s 0` (of its
transposed adjugate for odd `s`), with `m = ℓ + 1` or `ℓ` as `(b, s)` is deep or not. Its rows are
indexed by families `β` of exponent vectors `β s` of degree `n`, and `exponentOf β` sends `(b, s)`
to `β s b`. Let `G` be a filtration of `R` (an element of `G t` has level `t`), `u ≥ 0`, and
`α s d` real vectors of sum zero (potentials) with `|α s 0 b| ≤ u`. Let entry `(b, c)` of `ψ s d`
have level `α s (d + 1) b - α s d c - u` for `d ≤ ℓ`, and let `x (b, s) = ± α s m b`, with `+` for
even `s`. Then row `β` has level `∑ b s, β s b * x (b, s) - N n k (ℓ + 2) u`. -/
lemma substitutionOperator_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    (α : ZMod N → ℕ → Fin k → ℝ) (x : Fin k × ZMod N → ℝ) (u : ℝ) {β γ : Exponents N k n}
    (hα_zero : ∀ (s : ZMod N) (b : Fin k), |α s 0 b| ≤ u)
    (hα_sum : ∀ (s : ZMod N) (d : ℕ), ∑ b : Fin k, α s d b = 0)
    (hx : ∀ (b : Fin k) (s : ZMod N),
      x (b, s) = (if T.isEven s then 1 else -1) * α s (ℓ + T.deepIndicator r (b, s)) b)
    (hψ : ∀ s : ZMod N, ∀ d ≤ ℓ, ∀ b c : Fin k, ψ s d b c ∈ G (α s (d + 1) b - α s d c - u))
    (hu : 0 ≤ u) :
    T.substitutionOperator r ℓ n ψ β γ ∈
      G (weight x (exponentOf β) - N * n * k * (ℓ + 2) * u) := by
  let K : ℝ := k * ((ℓ + 2) * u)
  -- The potentials telescope along the product of `m ≤ ℓ + 1` factors.
  have h_prod (s : ZMod N) (m : ℕ) (hm : m ≤ ℓ + 1) (b c : Fin k) :
      ((range m).map (ψ s)).reverse.prod b c ∈ G (α s m b - (ℓ + 2) * u) := by
    have h_loss : (m + 1) * u ≤ (ℓ + 2) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast succ_le_succ hm) hu
    exact antitone (sub_le_sub_left h_loss (α s m b)) (reverse_prod_map_range_mem G
      (fun b ↦ le_of_abs_le (hα_zero s b)) (fun d hd ↦ hψ s d (by lia)) b c)
  have h_row (s : ZMod N) (b c : Fin k) :
    T.substitutionLetterMatrix r ℓ ψ s b c ∈ G (x (b, s) - K) := by
    rw [hx, substitutionLetterMatrix, of_apply]
    exact T.parityCofactor_mem G (by positivity) (hα_sum s _)
      (h_prod s _ (by grind [deepIndicator])) b c
  -- Pass to the symmetric powers, whose rows have degree `n`, and multiply over the letters.
  have h_letter (s : ZMod N) : weight (fun b : Fin k ↦ x (b, s) - K) (β s).val =
      weight (fun b : Fin k ↦ x (b, s)) (β s).val - n * K := by
    simp [weight_eq_sum, mul_sub, ← Finset.sum_mul, ← cast_sum, ← degree_eq_sum,
      Monomials.degree_eq]
  have h_split : weight x (exponentOf β) =
      ∑ s : ZMod N, weight (fun b : Fin k ↦ x (b, s)) (β s).val := by
    simp [exponentOf, weight_eq_sum, sum_prod_type_right]
  have h_level : weight x (exponentOf β) - N * n * k * (ℓ + 2) * u =
      ∑ s : ZMod N, weight (fun b : Fin k ↦ x (b, s) - K) (β s).val := by
    simp [h_letter, h_split, Finset.sum_sub_distrib, K]
    ring
  rw [h_level, substitutionOperator, kroneckerPi, of_apply]
  exact prod_mem_graded G _ _ fun s _ ↦ symPowMatrix_mem G (h_row s) (β s) (γ s)

/-! ### Weights of indices and the Gauss filtration -/

omit [NeZero N] in
lemma abs_indexWeight_le (b : Fin k) : |T.indexWeight ℓ a a' b| ≤ 1 / T.P ^ ℓ := by
  rw [indexWeight, abs_div, abs_pow, abs_cast]
  gcongr
  unfold rootVector
  split_ifs <;> simp

/-- Let `T` be a Frobenius cycle: its letters `s : ZMod N` are alternately even and odd
(`T.isEven`), `P = T.P` is its prime power and `q = T.q = P ^ N`. Let `a' = a + 1`. The defect
weight `T.defectWeight j a a' (b, s)` at a letter `j` is `± P ^ ((s - j) mod N) / (q - 1)` for
`b = a, a'` (positive at `a'` for even and at `a` for odd `s`, with `1` added to the positive weight
if `s = j`) and `0` for other `b`. For `j = i + ℓ`, this weight times `1 - 1 / q` is
`± ρ b / P ^ ℓ * P ^ (d + m) / q`, with `+` for even and `-` for odd `s`. Here `ρ b` is `1` at `a'`,
`-1` at `a` and else `0`, `ρ b / P ^ ℓ` is the index weight of `b`, `m = (s - d - i) mod N`, and
`d = ℓ + 1` or `ℓ` as `(b, s)` is deep for the cut at `a'` or not. -/
lemma mul_defectWeight_eq_indexWeight_mul (ha : (a : ℕ) + 1 = (a' : ℕ)) (i : ZMod N) (b : Fin k) :
    (1 - 1 / T.q) * T.defectWeight (i + ℓ) a a' (b, s) =
      (if T.isEven s then 1 else -1) * T.indexWeight ℓ a a' b *
        (T.P ^ (ℓ + T.deepIndicator a' (b, s) +
          (s - (ℓ + T.deepIndicator a' (b, s) : ℕ) - i).val) / T.q) := by
  have hlt : a < a' := Fin.lt_def.2 (by lia)
  -- The factor `P ^ ℓ` cancels against the denominator of the index weight, and
  -- `1 - 1 / q = (q - 1) / q`, so it is enough to compare the numerators.
  have h_cancel (e : ℕ) :
      T.indexWeight ℓ a a' b * (T.P ^ (ℓ + e + (s - (ℓ + e : ℕ) - i).val) / T.q) =
        rootVector a a' b * T.P ^ (e + (s - e - (i + ℓ)).val) / T.q := by
    have hP : (T.P : ℝ) ≠ 0 := (zero_lt_one.trans T.one_lt_P).ne'
    rw [show s - (ℓ + e : ℕ) - i = s - e - (i + ℓ) by grind, indexWeight, add_assoc, pow_add]
    field_simp
  suffices h_num :
      (if (b, s) = T.rootVar a a' s then (T.P : ℝ) ^ (1 + (s - 1 - (i + ℓ)).val) else 0) -
          (if (b, s) = T.rootVar a' a s then (T.P : ℝ) ^ (s - (i + ℓ)).val else 0) =
        (if T.isEven s then 1 else -1) * (rootVector a a' b * T.P ^ (T.deepIndicator a' (b, s) +
          (s - T.deepIndicator a' (b, s) - (i + ℓ)).val)) by
    have hq : (T.q : ℝ) - 1 ≠ 0 := (sub_pos.2 T.one_lt_q).ne'
    rw [mul_assoc, h_cancel, ← mul_div_assoc, ← h_num, defectWeight]
    have hq_ne : (T.q : ℝ) ≠ 0 := (zero_lt_one.trans T.one_lt_q).ne'
    field_simp
  -- Both sides vanish outside the rows `a`, `a'`. One of the variables `(a, s)`, `(a', s)` is deep
  -- and the other is not, which gives the two exponents in `defectWeight`.
  obtain rfl | hb := eq_or_ne b a
  · by_cases h_even : T.isEven s <;>
      simp [rootVar, rootVector, deepIndicator, h_even, hlt.ne, hlt.not_ge]
  obtain rfl | hb' := eq_or_ne b a' <;> by_cases h_even : T.isEven s <;>
    simp [rootVar, rootVector, deepIndicator, *]

/-- A polynomial has level `t` in the Gauss filtration over the `w`-adic filtration if and only if
its coefficient at each monomial `μ` is divisible by `w ^ ⌈t - weight ω μ⌉₊`. -/
lemma _root_.New.mem_gaussFiltration_adicFiltration_iff {σ : Type*} {w : O} {ω : σ → ℝ} {t : ℝ}
    {f : MvPolynomial σ O} :
    f ∈ gaussFiltration (adicFiltration w) ω t ↔
      ∀ μ : σ →₀ ℕ, w ^ ⌈t - weight ω μ⌉₊ ∣ f.coeff μ :=
  Iff.rfl

/-- If `f` lies at level `t` of the Gauss filtration with variable weights `ω` over
`adicFiltration 0`, then every monomial `μ` with `f.coeff μ ≠ 0` has `t ≤ weight ω μ`. -/
lemma _root_.New.le_weight_of_mem_gaussFiltration_zero {σ : Type*} {ω : σ → ℝ} {t : ℝ}
    {f : MvPolynomial σ O} (hf : f ∈ gaussFiltration (adicFiltration (0 : O)) ω t) {μ : σ →₀ ℕ}
    (hμ : f.coeff μ ≠ 0) : t ≤ weight ω μ := by
  by_contra! h_lt
  exact hμ (by simpa [zero_pow (ceil_pos.2 (sub_pos.2 h_lt)).ne'] using hf μ)

/-- The variable `X v` has level `ω v` in the Gauss filtration with variable weights `ω` over the
`w`-adic filtration. -/
lemma X_mem_gaussFiltration {σ : Type*} {w : O} {ω : σ → ℝ} {v : σ} :
    (X v : MvPolynomial σ O) ∈ gaussFiltration (adicFiltration w) ω (ω v) :=
  monomial_mem_gaussFiltration (by simp [weight_single])

/-! ### Change of frame -/

section

omit [NeZero N]

/-- Conjugate `Y` by `h⁻¹` through `T.embedding (s - d)`, raise the entries to the power `P ^ d`,
and conjugate by `h` through `T.embedding s`. Modulo `p` this is the entrywise `P ^ d`-th power of
`Y`, as `T.embedding (s - d)` to the power `P ^ d` is `T.embedding s` modulo `p`. -/
lemma p_dvd_letterConj_pow_sub {Y : Matrix (Fin k) (Fin k) O} {b c : Fin k} :
    (T.p : O) ∣ T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map (· ^ T.P ^ d)) b c -
      Y b c ^ T.P ^ d := by
  -- Modulo `p` the power `P ^ d` is a ring map `f`, and it carries `T.embedding (s - d)` to
  -- `T.embedding s`. So the two conjugations cancel.
  let Q : Type := O ⧸ Ideal.span {(T.p : O)}
  let π : O →+* Q := Ideal.Quotient.mk _
  have hp : π T.p = 0 := (eq_zero_iff_dvd _ _).2 dvd_rfl
  have h_add (x y : O) : π ((x + y) ^ T.P ^ d) = π (x ^ T.P ^ d) + π (y ^ T.P ^ d) := by
    simp only [← pow_mul, add_pow_prime_pow_eq T.prime, map_add, map_mul, hp, zero_mul, add_zero]
  let f : O →+* Q := RingHom.mk' (π.toMonoidHom.comp (powMonoidHom (T.P ^ d))) h_add
  have hf (x : O) : f x = π (x ^ T.P ^ d) := rfl
  have h_frob (x : W) : f (T.embedding (s - d) x) = π (T.embedding s x) := by
    rw [hf, eq_comm, ← sub_eq_zero, ← map_sub, eq_zero_iff_dvd]
    simpa using T.frobenius_pow_congr d (s - d) x
  let A : Matrix (Fin k) (Fin k) Q := h.val.map (π.comp (T.embedding s))
  let B : Matrix (Fin k) (Fin k) Q := h⁻¹.val.map (π.comp (T.embedding s))
  have hAB : A * B = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have h_outer (Z : Matrix (Fin k) (Fin k) O) : (T.letterConj h s Z).map π = A * Z.map π * B := by
    simp [letterConj, A, B, Matrix.map_mul]
  have h_inner : (T.letterConj h⁻¹ (s - d) Y).map f = B * Y.map f * A := by
    simp [letterConj, A, B, Matrix.map_mul, comp_def, h_frob]
  have h_pow (Z : Matrix (Fin k) (Fin k) O) : (Z.map (· ^ T.P ^ d)).map π = Z.map f :=
    Matrix.ext fun i j ↦ (hf (Z i j)).symm
  have h_cancel : (T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map (· ^ T.P ^ d))).map π =
      (Y.map (· ^ T.P ^ d)).map π :=
    calc _ = A * (B * Y.map f * A) * B := by rw [h_outer, h_pow, h_inner]
      _ = A * B * Y.map f * (A * B) := by simp only [mul_assoc]
      _ = (Y.map (· ^ T.P ^ d)).map π := by rw [hAB, one_mul, mul_one, h_pow]
  rw [← eq_zero_iff_dvd, map_sub, sub_eq_zero]
  exact congrFun₂ h_cancel b c

/-- The matrix `T.frobGenericMatrix s d` with a change of frame by `h`: the generic matrix of the
copy `s - d` is conjugated by `h⁻¹` through `T.embedding (s - d)`, its entries are raised to the
power `P ^ d`, and the result is conjugated by `h` through `T.embedding s`. -/
def conjFrobGenericMatrix (h : GL (Fin k) W) (s : ZMod N) (d : ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (ZMod N × Fin k × Fin k) O) :=
  (T.map C).letterConj h s
    (((T.map C).letterConj h⁻¹ (s - d) (of fun b c : Fin k ↦ X (s - d, b, c))).map (· ^ T.P ^ d))

lemma conjFrobGenericMatrix_one :
    T.conjFrobGenericMatrix (1 : GL (Fin k) W) = T.frobGenericMatrix := by
  ext s d b c : 4
  simp [conjFrobGenericMatrix, letterConj]

/-- A polynomial over `O` has level `t` (lies in `gaussFiltration (adicFiltration w) ω t`) if its
coefficient at each monomial `μ` is divisible by `w ^ ⌈t - weight ω μ⌉₊`. If all entries of `Y` have
level `t`, so have those of `ι(h) Y ι(h)⁻¹`, where `h` is in `GL_k(W)` and `ι = T.embedding s` maps
`W` to `O`, seen as constant polynomials (`T.map C`). -/
lemma letterConj_mem_gaussFiltration {σ : Type} {w : O} {ω : σ → ℝ} {t : ℝ}
    {Y : Matrix (Fin k) (Fin k) (MvPolynomial σ O)}
    (hY : ∀ b c : Fin k, Y b c ∈ gaussFiltration (adicFiltration w) ω t) (b c : Fin k) :
    (T.map C).letterConj h s Y b c ∈ gaussFiltration (adicFiltration w) ω t := by
  have hC (x : O) : C x ∈ gaussFiltration (adicFiltration w) ω 0 :=
    monomial_mem_gaussFiltration (by simp)
  have h_entry : (T.map C).letterConj h s Y b c =
      ∑ j : Fin k, ∑ i : Fin k,
        C (T.embedding s (h.val b i)) * Y i j * C (T.embedding s (h⁻¹.val j c)) := by
    simp [letterConj, map, Matrix.mul_apply, Finset.sum_mul]
  rw [h_entry]
  exact sum_mem fun j _ ↦ sum_mem fun i _ ↦ by
    simpa using mul_mem_graded (mul_mem_graded (hC _) (hY i j)) (hC _)

/-- Let all variable weights `ω v` have size at most `1 / T.P ^ d`. Then the entry `(b, c)` of
`T.conjFrobGenericMatrix h s d` has the level `t = T.P ^ d • ω (s - d, b, c)` of the same entry
`X (s - d, b, c) ^ T.P ^ d` without the conjugations: its coefficient at a monomial `μ` is divisible
by `T.sqrtPrime ^ ⌈t - weight ω μ⌉₊`. -/
lemma conjFrobGenericMatrix_mem_gaussFiltration {ω : ZMod N × Fin k × Fin k → ℝ}
    (hω : ∀ v : ZMod N × Fin k × Fin k, |ω v| ≤ 1 / T.P ^ d) (b c : Fin k) :
    T.conjFrobGenericMatrix h s d b c ∈
      gaussFiltration (adicFiltration T.sqrtPrime) ω (T.P ^ d • ω (s - d, b, c)) := by
  -- Only monomials of weight at least `-1` occur. At these the wanted power of `T.sqrtPrime`
  -- divides `T.sqrtPrime ^ 2 = p`, and modulo `p` the conjugations cancel.
  let G : ℝ → AddSubgroup (MvPolynomial (ZMod N × Fin k × Fin k) O) :=
    gaussFiltration (adicFiltration 0) ω
  set M : MvPolynomial (ZMod N × Fin k × Fin k) O := T.conjFrobGenericMatrix h s d b c
  set t : ℝ := T.P ^ d • ω (s - d, b, c)
  have hX (v : ZMod N × Fin k × Fin k) : X v ∈ G (-(1 / T.P ^ d)) :=
    antitone (neg_le_of_abs_le (hω v)) X_mem_gaussFiltration
  have h_supp : M ∈ G (T.P ^ d • -(1 / T.P ^ d)) :=
    T.letterConj_mem_gaussFiltration (fun i j ↦ pow_mem_graded _
      (T.letterConj_mem_gaussFiltration (fun x y ↦ hX (s - d, x, y)) i j)) b c
  refine mem_gaussFiltration_adicFiltration_iff.2 fun μ ↦ ?_
  obtain hμ | hμ := eq_or_ne (M.coeff μ) 0
  · simp [hμ]
  have h_weight : -1 ≤ weight ω μ := by
    simpa [T.prime.ne_zero] using le_weight_of_mem_gaussFiltration_zero h_supp hμ
  have h_level : t ≤ 1 := by
    have hp : T.p ≠ 0 := T.prime.ne_zero
    simpa [t, field, mul_comm] using le_of_abs_le (hω (s - d, b, c))
  have h_le : ⌈t - weight ω μ⌉₊ ≤ 2 := ceil_le.2 (by push_cast; linarith)
  have h_mod : C (T.sqrtPrime ^ 2) ∣ M - X (s - d, b, c) ^ T.P ^ d := by
    rw [T.sqrtPrime_sq, map_natCast]
    exact (T.map C).p_dvd_letterConj_pow_sub
  have h_error : T.sqrtPrime ^ 2 ∣ M.coeff μ - (X (s - d, b, c) ^ T.P ^ d).coeff μ := by
    simpa only [coeff_sub] using (C_dvd_iff_dvd_coeff _ _).1 h_mod μ
  have h_main : T.sqrtPrime ^ ⌈t - weight ω μ⌉₊ ∣ (X (s - d, b, c) ^ T.P ^ d).coeff μ :=
    mem_gaussFiltration_adicFiltration_iff.1 (pow_mem_graded _ X_mem_gaussFiltration) μ
  exact (dvd_sub_left h_main).1 ((pow_dvd_pow _ h_le).trans h_error)

end

/-- Let `ν` be a monomial in the variables `(j, b, c)`, the entries of `N` generic `k × k` matrices,
let `P = T.P`, `q = P ^ N` and `ρ = rootVector a a' = e_{a'} - e_a`. The weight
`T.entryWeight ℓ a a' i (j, b, c)` is `ρ b / P ^ ℓ` if `j = i` and else
`P ^ ((j - i) mod N) / q * (ρ b - ρ c) / P ^ ℓ`. Its sum over the variables of `ν` equals
`T.copyWeight ℓ a a' i ν`, which is defined copy by copy from the sums of `ρ` over the row indices
and over the column indices. -/
lemma weight_entryWeight (i : ZMod N) (ν : ZMod N × Fin k × Fin k →₀ ℕ) :
    weight (T.entryWeight ℓ a a' i) ν = T.copyWeight ℓ a a' i ν := by
  let row (j : ZMod N) : ℤ := weight (fun v : Fin k × Fin k ↦ rootVector a a' v.1) (ν.curry j)
  let col (j : ZMod N) : ℤ := weight (fun v : Fin k × Fin k ↦ rootVector a a' v.2) (ν.curry j)
  let copy (j : ZMod N) : ℝ := weight (fun v ↦ T.entryWeight ℓ a a' i (j, v)) (ν.curry j)
  have h_self : copy i = row i / T.P ^ ℓ := by
    simp [copy, row, entryWeight, indexWeight, weight_eq_sum, Finset.sum_div, mul_div_assoc]
  have h_other (j : ZMod N) (hj : j ∈ Finset.univ.erase i) :
      copy j = T.P ^ (j - i).val / T.q * (row j - col j) / T.P ^ ℓ := by
    simp only [copy, row, col, entryWeight, scaledIndexWeight,
      ite_eq_right (Finset.ne_of_mem_erase hj), indexWeight, weight_eq_sum, Int.cast_sum,
      ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, nsmul_eq_mul, Int.cast_mul,
        Int.cast_natCast]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  calc weight (T.entryWeight ℓ a a' i) ν = ∑ j : ZMod N, copy j := by
        simp only [copy, weight_eq_sum, sum_prod_type (α₁ := ZMod N), Finsupp.curry_apply]
    _ = T.copyWeight ℓ a a' i ν := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), h_self, Finset.sum_congr rfl h_other,
          copyWeight, add_div, Finset.sum_div]

/-- The scaled index weight of an index at an exponent `m ≤ N` has size at most `1 / P ^ ℓ`. -/
lemma abs_scaledIndexWeight_le {m : ℕ} (hm : m ≤ N) (b : Fin k) :
    |T.scaledIndexWeight ℓ a a' m b| ≤ 1 / T.P ^ ℓ := by
  rw [scaledIndexWeight, abs_mul]
  refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (T.abs_indexWeight_le b)
  rw [abs_of_nonneg (by positivity), div_le_one (zero_lt_one.trans T.one_lt_q), cast_pow T.P N]
  exact pow_le_pow_right₀ T.one_lt_P.le hm

/-- For every copy `i` and every entry `v` (a copy together with a row and a column index), the
weight `T.entryWeight ℓ a a' i v` has absolute value at most `2 / T.P ^ ℓ`. -/
lemma abs_entryWeight_le (i : ZMod N) (v : ZMod N × Fin k × Fin k) :
    |T.entryWeight ℓ a a' i v| ≤ 2 / T.P ^ ℓ := by
  rw [entryWeight, show (2 / T.P ^ ℓ : ℝ) = 1 / T.P ^ ℓ + 1 / T.P ^ ℓ by ring]
  split_ifs
  · exact (T.abs_indexWeight_le _).trans (le_add_of_nonneg_left (by positivity))
  · have hm : (v.1 - i).val ≤ N := (v.1 - i).val_lt.le
    grw [abs_sub, T.abs_scaledIndexWeight_le hm, T.abs_scaledIndexWeight_le hm]

/-- Let `P = T.P`. The entry `(b, c)` of
`T.frobGenericMatrix s d` is the variable `(s - d, b, c)` to the power `P ^ d`, so its weight at the
copy `i` is `P ^ d` times `T.entryWeight`. For `d ≤ N` this weight differs by at most `1 / P ^ ℓ`
from the scaled index weight of `b` at the exponent `d + 1 + (s - (d + 1) - i) mod N` less that of
`c` at the exponent `d + (s - d - i) mod N`. -/
lemma abs_scaledIndexWeight_sub_scaledIndexWeight_sub_entryWeight_le (hd : d ≤ N) (i : ZMod N)
    (b c : Fin k) :
    |T.scaledIndexWeight ℓ a a' (d + 1 + (s - (d + 1 : ℕ) - i).val) b -
        T.scaledIndexWeight ℓ a a' (d + (s - d - i).val) c -
      T.P ^ d * T.entryWeight ℓ a a' i (s - d, b, c)| ≤ 1 / T.P ^ ℓ := by
  have h_shift (m : ℕ) (b : Fin k) :
      T.scaledIndexWeight ℓ a a' (d + m) b = T.P ^ d * T.scaledIndexWeight ℓ a a' m b := by
    unfold scaledIndexWeight
    ring
  have h_succ : d + 1 + (s - (d + 1 : ℕ) - i).val =
      d + if s - d = i then N else (s - d - i).val := by
    rw [add_assoc, cast_succ, ← sub_sub, one_add_val_sub_one_sub]
  rw [h_succ, entryWeight]
  split_ifs with h_copy
  · -- Only the scaled index weight of `c` is left.
    have h_full : T.scaledIndexWeight ℓ a a' N b = T.indexWeight ℓ a a' b := by
      rw [scaledIndexWeight, ← cast_pow T.P N, div_self (zero_lt_one.trans T.one_lt_q).ne', mul_one]
    simpa [h_copy, h_shift, h_full] using T.abs_scaledIndexWeight_le hd c
  · -- The difference of the scaled index weights is exactly the weight of the entry.
    simp [h_shift, mul_sub]

end

variable {r ℓ n : ℕ} {a a' : Fin k}

/-- Let `T` be a Frobenius cycle, with letters `s : ZMod N`, prime power `P = T.P`, `q = P ^ N` and
`w = T.sqrtPrime`, `w ^ 2 = p`. Let `a' = a + 1`, `ℓ ≤ N`, `|ε| ≤ 1 / 2` and `ρ = e_{a'} - e_a`.
Take a generic matrix `X_j` for each `j : ZMod N`, and give its entry `(b, c)` the weight `ε` times
`T.entryWeight ℓ a a' i (j, b, c)`, which is `ρ b / P ^ ℓ` if `j = i` and else
`P ^ ((j - i) mod N) / q * (ρ b - ρ c) / P ^ ℓ`. The matrix `T.substitutionOperator` is the
Kronecker product over `s` of `n`-th symmetric powers of products (transposed adjugates of products
for odd `s`) of the entrywise powers `P ^ d`, `d ≤ ℓ` in deep rows and `d < ℓ` in the others, of the
`X_{s - d}`, taken between conjugations by `h⁻¹` and `h`; its rows `β` are monomials of degree `n`
in the variables `(b, s)` of each letter `s`. The defect of `β` at `i + ℓ` is the sum over its
variables of `T.defectWeight`, which is `± P ^ ((s - i - ℓ) mod N) / (q - 1)` for `b = a, a'` (`+`
at `a'` for even and at `a` for odd `s`, plus `1` there if `s = i + ℓ`) and else `0`. Then the
entries of row `β` have level `t = ε (1 - 1 / q) defect - N n k (ℓ + 2) / (2 P ^ ℓ)`: the
coefficient of a monomial `ν` is divisible by `w ^ ⌈t - weight of ν⌉₊`. -/
lemma substitutionOperator_conj_mem_gaussFiltration (ha : (a : ℕ) + 1 = (a' : ℕ)) (i : ZMod N)
    (hℓ_le : ℓ ≤ N) (h : GL (Fin k) W) {ε : ℝ} (hε : |ε| ≤ 2⁻¹) (β γ : Exponents N k n) :
    T.substitutionOperator a' ℓ n (T.conjFrobGenericMatrix h) β γ ∈
      gaussFiltration (adicFiltration T.sqrtPrime) (ε • T.entryWeight ℓ a a' i)
        (weight ((ε * (1 - 1 / T.q)) • T.defectWeight (i + ℓ) a a') (exponentOf β) -
          N * n * k * (ℓ + 2) / (2 * T.P ^ ℓ)) := by
  set ω : ZMod N × Fin k × Fin k → ℝ := ε • T.entryWeight ℓ a a' i
  set u : ℝ := 2⁻¹ * (1 / T.P ^ ℓ)
  have h_scale {y z : ℝ} (hy : |y| ≤ z) : |ε * y| ≤ 2⁻¹ * z :=
    (abs_mul ε y).trans_le (mul_le_mul hε hy (abs_nonneg y) (by norm_num))
  have h_small {d : ℕ} (hd : d ≤ ℓ) (v : ZMod N × Fin k × Fin k) : |ω v| ≤ 1 / T.P ^ d :=
    calc |ω v| ≤ 2⁻¹ * (2 / T.P ^ ℓ) := h_scale (T.abs_entryWeight_le i v)
      _ = 1 / T.P ^ ℓ := by ring
      _ ≤ 1 / T.P ^ d := one_div_pow_le_one_div_pow_of_le T.one_lt_P.le hd
  -- The potential of the factor `d` at the letter `s` has the exponent `d + m`, where
  -- `s - d = i + m` and `m < N`.
  let α (s : ZMod N) (d : ℕ) (b : Fin k) : ℝ :=
    ε * T.scaledIndexWeight ℓ a a' (d + (s - d - i).val) b
  have hα_zero (s : ZMod N) (b : Fin k) : |α s 0 b| ≤ u :=
    h_scale (T.abs_scaledIndexWeight_le (by simpa using (ZMod.val_lt _).le) b)
  have hα_sum (s : ZMod N) (d : ℕ) : ∑ b : Fin k, α s d b = 0 := by
    simp [α, scaledIndexWeight, indexWeight, rootVector, ← Finset.mul_sum, ← Finset.sum_mul,
      ← Finset.sum_div]
  have h_last (b : Fin k) (s : ZMod N) :
      ((ε * (1 - 1 / T.q)) • T.defectWeight (i + ℓ) a a') (b, s) =
        (if T.isEven s then 1 else -1) * α s (ℓ + T.deepIndicator a' (b, s)) b := by
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc, T.mul_defectWeight_eq_indexWeight_mul ha i]
    simp only [α, scaledIndexWeight]
    ring
  have h_step (s : ZMod N) (d : ℕ) (hd : d ≤ ℓ) (b c : Fin k) :
      α s (d + 1) b - α s d c - u ≤ T.P ^ d • ω (s - d, b, c) := by
    have h_close : |α s (d + 1) b - α s d c - T.P ^ d • ω (s - d, b, c)| ≤ u := by
      simpa only [α, ω, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, cast_pow T.P d, mul_sub,
        mul_left_comm ε] using
        h_scale (T.abs_scaledIndexWeight_sub_scaledIndexWeight_sub_entryWeight_le
          (hd.trans hℓ_le) i b c)
    linarith [le_of_abs_le h_close]
  have h_factor (s : ZMod N) (d : ℕ) (hd : d ≤ ℓ) (b c : Fin k) :
      T.conjFrobGenericMatrix h s d b c ∈
        gaussFiltration (adicFiltration T.sqrtPrime) ω (α s (d + 1) b - α s d c - u) :=
    antitone (h_step s d hd b c) (T.conjFrobGenericMatrix_mem_gaussFiltration (h_small hd) b c)
  rw [show (N * n * k * (ℓ + 2) / (2 * T.P ^ ℓ) : ℝ) = N * n * k * (ℓ + 2) * u by ring]
  exact T.substitutionOperator_mem _ α _ u hα_zero hα_sum h_last h_factor (by positivity)

/-- If `2 n ≤ T.q`, the defect `Δ` at the letter `i` along the root `(a, a')` of a monomial `β` of
degree `n` in each letter (the sum of `T.defectWeight i a a'` over `exponentOf β`) satisfies
`|Δ - (1 - 1 / T.q) Δ| ≤ 1`. -/
lemma abs_defect_sub_mul_le_one (i : ZMod N) (β : Exponents N k n) (hn : 2 * n ≤ T.q) :
    |weight (T.defectWeight i a a') (exponentOf β) -
      (1 - 1 / T.q) * weight (T.defectWeight i a a') (exponentOf β)| ≤ 1 := by
  set Δ : ℝ := weight (T.defectWeight i a a') (exponentOf β)
  have hq : (0 : ℝ) < T.q := zero_lt_one.trans T.one_lt_q
  have h_size : |Δ| ≤ 2 * n := T.abs_weight_defectWeight_le fun s ↦ by
    simpa [exponentOf, degree_eq_sum, ← cast_sum] using (β s).degree_eq.le
  rw [show Δ - (1 - 1 / T.q) * Δ = Δ / T.q by ring, abs_div, abs_of_pos hq, div_le_one hq]
  exact h_size.trans (by exact_mod_cast hn)

/-- Weight and defect. Let `T` be a Frobenius cycle, with letters `s : ZMod N` (even or odd), ring
maps `W → O`, prime `p`, the power `P = T.P` of `p`, `q = P ^ N` and `w = T.sqrtPrime` in `O` with
`w ^ 2 = p`. Let `a' = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ`, `ℓ ≤ N` and `h` in `GL_k(W)`. Take a generic
matrix `X_j` for each `j : ZMod N` (a copy). The matrix `T.substitutionOperator a' ℓ n` is the
Kronecker product over `s` of `n`-th symmetric powers of products (transposed adjugates of products
for odd `s`) of the entrywise powers `P ^ d` of the `X_{s - d}`, taken between conjugations by `h⁻¹`
and `h` (`T.conjFrobGenericMatrix h`); here `d ≤ ℓ` in the rows `b ≥ a'` for even and `b < a'` for
odd `s`, and `d < ℓ` in the others. Its rows `β` are monomials of degree `n` in the variables
`(b, s)` of each letter `s`.

* The defect of `β` at `i + ℓ` is the sum over its variables of `T.defectWeight`, which is
  `± P ^ ((s - i - ℓ) mod N) / (q - 1)` for `b = a, a'` (`+` at `a'` for even and at `a` for odd
  `s`, plus `1` there if `s = i + ℓ`) and else `0`.
* The weight `T.copyWeight` at the copy `i` of a monomial `ν` in the entries of the `X_j` is the sum
  over its variables `(j, b, c)` of `ρ b / P ^ ℓ` if `j = i` and else of
  `P ^ ((j - i) mod N) / q * (ρ b - ρ c) / P ^ ℓ`, where `ρ = e_{a'} - e_a`.

If the coefficient of `ν` in the entry `(β, γ)` is not divisible by `w ^ c`, then the weight of `ν`
is within `defectThreshold k c = 3 k c` of the defect of `β`. -/
lemma abs_defect_sub_copyWeight_le (ha : (a : ℕ) + 1 = (a' : ℕ)) (i : ZMod N)
    (hn_le : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ_le : ℓ ≤ N) (h : GL (Fin k) W) {c : ℕ}
    {β γ : Exponents N k n} {ν : ZMod N × Fin k × Fin k →₀ ℕ}
    (h_coeff : ¬T.sqrtPrime ^ c ∣
      (T.substitutionOperator a' ℓ n (T.conjFrobGenericMatrix h) β γ).coeff ν) :
    |weight (T.defectWeight (i + ℓ) a a') (exponentOf β) - T.copyWeight ℓ a a' i ν| ≤
      defectThreshold k c := by
  -- Let `D` be the weight of `ν` and `E` be `1 - 1 / q` times the defect `Δ`. For `ε = ± 1 / 2`
  -- the coefficient is divisible by `w ^ ⌈ε (E - D) - L⌉₊`, where `L ≤ 1 / 2`. This
  -- exponent is at most `c`, so `|E - D| ≤ 2 c + 1`. Also `|Δ - E| ≤ 1`, and `2 c + 2 ≤ 3 k c`
  -- because `k ≥ 2` and `c ≥ 1`.
  set Δ : ℝ := weight (T.defectWeight (i + ℓ) a a') (exponentOf β) with hΔ
  let E : ℝ := (1 - 1 / T.q) * Δ
  set D : ℝ := T.copyWeight ℓ a a' i ν with hD
  let L : ℝ := N * n * k * (ℓ + 2) / (2 * T.P ^ ℓ)
  have h_loss : L ≤ 2⁻¹ := by
    have h_cast : (N * n * k * (ℓ + 2) : ℝ) ≤ T.P ^ ℓ := by exact_mod_cast hn_le
    rw [div_le_iff₀ (mul_pos two_pos (pow_pos (zero_lt_one.trans T.one_lt_P) ℓ))]
    linarith
  have hn_le_q : 2 * n ≤ T.q :=
    calc 2 * n = 1 * n * 1 * 2 := by ring
      _ ≤ N * n * k * (ℓ + 2) := by
        gcongr
        exacts [NeZero.pos N, a.pos, Nat.le_add_left 2 ℓ]
      _ ≤ T.q := hn_le.trans (Nat.pow_le_pow_right (pow_pos T.prime.pos T.frobExp) hℓ_le)
  have h_bound {ε : ℝ} (hε : |ε| ≤ 2⁻¹) : ε * (E - D) ≤ c + 2⁻¹ := by
    have h_defect :
        weight ((ε * (1 - 1 / T.q)) • T.defectWeight (i + ℓ) a a') (exponentOf β) = ε * E := by
      simp [E, hΔ, weight_eq_sum, Finset.mul_sum, mul_left_comm, mul_assoc]
    have h_weight : weight (ε • T.entryWeight ℓ a a' i) ν = ε * D := by
      simp [hD, ← T.weight_entryWeight, weight_eq_sum, Finset.mul_sum, mul_left_comm]
    have h_dvd : T.sqrtPrime ^ ⌈ε * E - L - ε * D⌉₊ ∣
        (T.substitutionOperator a' ℓ n (T.conjFrobGenericMatrix h) β γ).coeff ν := by
      rw [← h_defect, ← h_weight]
      exact mem_gaussFiltration_adicFiltration_iff.1
        (T.substitutionOperator_conj_mem_gaussFiltration ha i hℓ_le h hε β γ) ν
    by_contra! h_large
    exact h_coeff ((pow_dvd_pow _ (lt_ceil.2 (by linarith)).le).trans h_dvd)
  have h_pos : 2⁻¹ * (E - D) ≤ c + 2⁻¹ := h_bound (by norm_num)
  have h_neg : -2⁻¹ * (E - D) ≤ c + 2⁻¹ := h_bound (by norm_num)
  obtain ⟨h_rest_lower, h_rest_upper⟩ : -1 ≤ Δ - E ∧ Δ - E ≤ 1 :=
    abs_le.1 (T.abs_defect_sub_mul_le_one (i + ℓ) β hn_le_q)
  have h_threshold : (2 * c + 2 : ℝ) ≤ defectThreshold k c := by
    have hc : 1 ≤ c := Nat.pos_of_ne_zero fun h_zero ↦ h_coeff (by simp [h_zero])
    exact_mod_cast (by nlinarith [show 2 ≤ k by lia] : 2 * c + 2 ≤ 3 * k * c)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### Degrees -/

/-- Let `T` be a Frobenius cycle with letters `s : ZMod N` and prime power `P = T.P`. Take a generic
matrix with entries `X (j, b, c)` for each `j : ZMod N` (a copy); `T.frobGenericMatrix s d` is the
entrywise power `P ^ d` of the copy `s - d`. The matrix `T.substitutionOperator r ℓ n` is the
Kronecker product over `s` of `n`-th symmetric powers of products (transposed adjugates of products
for odd `s`) of these for `d < ℓ + 1` or `d < ℓ`, as the side of `r` on which the row lies and the
parity of `s` decide. Its rows and columns `β`, `γ` are families of exponent vectors of degree `n`,
one for each letter. A monomial `ν` that occurs in an entry has degree at most
`N n k (ℓ + 2) P ^ ℓ` in the variables of each copy `j`. -/
lemma degree_le_of_coeff_substitutionOperator {β γ : Exponents N k n}
    {ν : ZMod N × Fin k × Fin k →₀ ℕ}
    (hν : (T.substitutionOperator r ℓ n T.frobGenericMatrix β γ).coeff ν ≠ 0) (j : ZMod N) :
    degree (ν.curry j) ≤ N * n * k * (ℓ + 2) * T.P ^ ℓ := by
  -- Give the variables of the copy `j` weight `-1`. Level `-t` of the Gauss filtration over
  -- `adicFiltration 0` consists of the polynomials of degree at most `t` in the copy `j`.
  let ω (v : ZMod N × Fin k × Fin k) : ℝ := if v.1 = j then -1 else 0
  have h_weight : weight ω ν = -((degree (ν.curry j) : ℕ) : ℝ) := by
    simp [ω, degree_eq_sum, sum_prod_type_right, weight_eq_sum]
  have h_entry (s : ZMod N) (d : ℕ) (hd : d ≤ ℓ) (b c : Fin k) : T.frobGenericMatrix s d b c ∈
      gaussFiltration (adicFiltration (0 : O)) ω (0 - 0 - T.P ^ ℓ) := by
    refine antitone ?_ (pow_mem_graded _ X_mem_gaussFiltration)
    calc (0 - 0 - T.P ^ ℓ : ℝ) ≤ T.P ^ d • (-1 : ℝ) := by
          simpa using pow_le_pow_right₀ T.one_lt_P.le hd
      _ ≤ T.P ^ d • ω (s - d, b, c) := by
          gcongr
          grind
  -- All potentials are `0`, and each factor loses `P ^ ℓ`.
  have h_mem : T.substitutionOperator r ℓ n T.frobGenericMatrix β γ ∈
      gaussFiltration (adicFiltration 0) ω
        (weight 0 (exponentOf β) - N * n * k * (ℓ + 2) * T.P ^ ℓ) :=
    T.substitutionOperator_mem _ (α := 0) (x := 0) (u := T.P ^ ℓ) (hα_zero := by simp)
      (hα_sum := by simp) (hx := by simp) (hψ := h_entry) (hu := by positivity)
  rify
  simpa [h_weight, weight_eq_sum 0] using le_weight_of_mem_gaussFiltration_zero h_mem hν

end New.FrobeniusCycle

end
