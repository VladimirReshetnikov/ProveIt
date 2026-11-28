import Lib.Base

/-!
# Schur modules: semi-invariants, minors, Fock pairing, Schur and Gram matrices

This file sets up a polynomial model of the representations of products of general linear groups
over any commutative ring `R`. The variables `X (a, i)` of `New.MatrixPoly m R` form an array with
rows `a : m` and columns `i : ℕ`. A colour map `c` assigns each row a place `τ`, and a weight `κ`
gives the number `κ τ h` of columns of height `h` at `τ`. `New.nabla R c l` consists of the `f` with
`f(y b) = ∏ b(τ, i, i) ^ l(τ, i) · f(y)` for upper triangular `b`, one matrix for each colour, and a
chosen set of products of minors is taken as its basis. The Weyl module is the dual module, written
in the dual basis as `New.WeylIndexFamily n κ → R`; `Lib.GLn.SchurModule.TensorModel` embeds it into
a tensor product of exterior powers. Left substitution `f ↦ f(z y)` and the Fock pairing
`⟨p, q⟩ = p(∂) q (0)` are the main tools. The rows of the Schur matrix expand the substituted basis
elements, so it acts on the Weyl module, and the Gram matrix is the coefficient matrix of the kernel
`New.weylKernel` in the basis.

## Main definitions and results

* `New.jet`, `New.fockPairing`: the pairing `P(∂) F` at `0`, with power series and with polynomials;
  `New.fockPairing_linSubst` computes adjoints of linear substitutions.
* `New.nabla`, `New.nablaFamily`: the semi-invariants under upper triangular matrices acting on
  columns.
* `New.tableauPoly`, `New.IsTableauBasis`, `New.nablaBasis`: products of minors, and a chosen basis
  among them.
* `New.schur`, `New.weylGram`, `New.weylEval`: the matrix of `f ↦ f(z y)`, the Gram matrix and the
  evaluation vectors in that basis.
* `New.mem_nabla`, `New.minor_mem_nabla`, `New.rowSubst_mem_nabla`: membership as an identity over
  all algebras; minors are members; left substitution `f ↦ f(z y)` (`New.rowSubst`) keeps the
  weight.
* `New.fockPairing_comm`, `New.fockPairing_rowSubst`, `New.fockPairing_star_self_pos`: the pairing
  `⟨p, q⟩ = p(∂) q (0)` is symmetric, the adjoint of `New.rowSubst z` is substitution by the
  transposes, and `⟨p̄, p⟩ > 0` for `p ≠ 0`.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.MinorBasis` for sources.
-/

noncomputable section

/-!
## The polynomial model and its basic objects

Bases are chosen by `Classical.epsilon`. Coordinates in `schur` and `weylGram` are chosen by
`Function.invFun`.
-/

section Defs

open MvPolynomial Module Finset Matrix Nat Sigma Finsupp Fintype Function

namespace New

variable {σ Φ m R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  (n n' : Φ → Type) [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] (c : m → Φ) (N e : Φ → ℕ)
  (κ : Φ → ℕ → ℕ) (τ : Φ)

/-- For a row colouring `c` and arrays `b` and `y`, the array `y b` has `(a, j)` entry
`Σ_{i≤j} y(a,i) b(c(a),i,j)`; here `x = (a, j)`. It uses the upper triangular part of `b` at the
colour of `a`. -/
def borelMul (b : Φ × ℕ × ℕ → R) (y : m × ℕ → R) (x : m × ℕ) : R :=
  ∑ i ∈ range (x.snd + 1), y (x.fst, i) * b (c x.fst, i, x.snd)

/-- For bounds `N` and column multiplicities `κ` (`κ τ h` columns of height `h` at `τ`, for
`h < N τ`), the finitely supported weight whose value at `(τ, i)`, columns numbered from 0, is the
sum of `κ τ h` over `i < h < N τ`. -/
def diagramWeight : Φ × ℕ →₀ ℕ :=
  ∑ τ : Φ, ∑ h ∈ range (N τ), κ τ h • ∑ i ∈ range h, Finsupp.single (τ, i) 1

variable (m R)

/-! ### Polynomial arrays, the Fock pairing, minors, semi-invariants and fillings -/

/-- Polynomials over `R` in an array of variables `X (a, i)`, with rows `a : m` and columns
`i : ℕ`. -/
abbrev MatrixPoly : Type := MvPolynomial (m × ℕ) R

/-- The type of fillings assigning, for each height h<N, to each of k(h) columns an h-tuple of
elements of m, with no ordering condition. -/
abbrev Tableau (N : ℕ) (k : ℕ → ℕ) : Type := ∀ h : Fin N, Fin (k h) → Fin h → m

variable {m} {h N : ℕ} {k : ℕ → ℕ}

/-- The bilinear pairing of a polynomial P with a formal power series F giving P(∂)F(0), the sum
over exponents d of d! times both d-th coefficients. -/
def jet : MvPolynomial σ R →ₗ[R] MvPowerSeries σ R →ₗ[R] R :=
  (basisMonomials σ R).constr ℕ fun d ↦ (d.prod fun _ j ↦ j !) • MvPowerSeries.coeff d

/-- The bilinear form on polynomials ⟨P,Q⟩ = P(∂)Q(0), for which monomials are orthogonal and
⟨x^d,x^d⟩ = d!. -/
@[local simp]
def fockPairing : LinearMap.BilinForm R (MvPolynomial σ R) :=
  (jet R).compl₂ (coeToMvPowerSeries.algHom R).toLinearMap

/-- For an h-tuple I of rows, the polynomial determinant of the h×h matrix of variables in rows
I and the first h columns. -/
def minor (I : Fin h → m) : MatrixPoly m R := det (of fun a b ↦ X (I a, b))

/-- For a row colouring `c : m → Φ` and a weight `l`, the module of Borel semi-invariants: the
polynomials `f` with `f(yβ) = ∏ β_{τ,ii}^{l(τ,i)} f(y)` for generic upper triangular matrices `β_τ`,
one per colour. -/
def nabla (l : Φ × ℕ →₀ ℕ) : Submodule R (MatrixPoly m R) :=
  -- Both maps go to polynomials over `R[b]`, in the entries `b (τ, i, j)` of a generic upper
  -- triangular matrix: right translation by `b`, and multiplication by the character of `l`.
  (aeval (borelMul c (C ∘ X (R := R)) X)).toLinearMap.eqLocus
    ((l.prod fun p j ↦ X (R := R) (p.fst, p.snd, p.snd) ^ j) • (aeval X).toLinearMap)

/-- For a filling `T` with entries in `σ` and a map `e : σ → m` to the rows, the product over
the columns of `T` of the minors `New.minor` whose rows are the `e`-images of the column's
entries. -/
def tableauPoly (e : σ → m) (T : Tableau σ N k) : MatrixPoly m R :=
  ∏ h : Fin N, ∏ j : Fin (k h), minor (m := m) R (e ∘ T h j)

/-- For x in ℂ^N and l : ℕ → ℕ, the alternant det(x_i^{l(N−1−j)+j}), 0 ≤ i, j < N, if l(N) = 0,
and zero otherwise. -/
def GL.alternant (x : Fin N → ℂ) (l : ℕ → ℕ) : ℂ :=
  if l N = 0 then det (of fun i j ↦ x i ^ (l j.rev + j)) else 0

/-- The set `s` of fillings is a standard set, in two parts: (a) over every commutative ring the
minor products of `s` form a basis of the span of all minor products; (b) for every enumeration `e`
of the rows and every `x : m → ℂ`, `(Σ_{T∈s} x^T) a_0(x) = a_λ(x)`. Here `x^T` is the product of `x`
over the entries of `T`, `a` is the alternant `New.GL.alternant`, and `λ(i)` is the sum of `k(h)`
over `i < h < N`. -/
def IsTableauBasis (s : Finset (Tableau m N k)) : Prop :=
  -- (a) the minor products of `s` are a basis of the span of all minor products
  (∀ (R : Type) [CommRing R],
    let v (T : Tableau m N k) := tableauPoly R id T
    LinearIndepOn R v s ∧ ∀ T : Tableau m N k, v T ∈ Submodule.span R (v '' s)) ∧
  -- (b) the Weyl character formula, for every enumeration `e` of the rows
  ∀ (M : ℕ) (e : Fin M ≃ m) (x : m → ℂ),
    (∑ T ∈ s, ∏ h : Fin N, ∏ j : Fin (k h), ∏ a : Fin h, x (T h j a)) * GL.alternant (x ∘ e) 0 =
      GL.alternant (x ∘ e) fun i ↦ ∑ h ∈ Ioo i N, k h

/-- For a standard set `s` (`IsTableauBasis`), over every commutative ring `R` the minor products
`tableauPoly R id T`, `T ∈ s`, are linearly independent. -/
lemma IsTableauBasis.linearIndepOn {s : Finset (Tableau m N k)} (hs : IsTableauBasis s)
    (R : Type) [CommRing R] :
    LinearIndepOn R (tableauPoly R id) (s : Set (Tableau m N k)) :=
  (hs.left R).left

/-- For a standard set `s`, over every commutative ring `R` the minor product of every filling `T`
lies in the span of the minor products of the members of `s`. -/
lemma IsTableauBasis.mem_span {s : Finset (Tableau m N k)} (hs : IsTableauBasis s)
    (R : Type) [CommRing R] (T : Tableau m N k) :
    tableauPoly R id T ∈ Submodule.span R (tableauPoly R id '' (s : Set (Tableau m N k))) :=
  (hs.left R).right T

/-- The Weyl character formula for a standard set `s`: for every enumeration `e : Fin M ≃ m` of
the rows and every `x : m → ℂ`, `(Σ_{T ∈ s} x^T) a_0(x) = a_λ(x)`, where `x^T` is the product of
`x` over the entries of `T`, `a` is `New.GL.alternant` and `λ i` is the sum of `k h` over
`i < h < N`. -/
lemma IsTableauBasis.weyl_character_formula {s : Finset (Tableau m N k)} (hs : IsTableauBasis s)
    (M : ℕ) (e : Fin M ≃ m) (x : m → ℂ) :
    (∑ T ∈ s, ∏ h : Fin N, ∏ j : Fin (k h), ∏ a : Fin h, x (T h j a)) * GL.alternant (x ∘ e) 0 =
      GL.alternant (x ∘ e) fun i ↦ ∑ h ∈ Ioo i N, k h :=
  hs.right M e x

/-- A set `s` of fillings is a standard set if, over every commutative ring, its minor products are
linearly independent and span all minor products, and it satisfies the Weyl character formula. -/
lemma IsTableauBasis.of_linearIndepOn_of_mem_span_of_character {s : Finset (Tableau m N k)}
    (h_indep : ∀ (R : Type) [CommRing R],
      LinearIndepOn R (tableauPoly R id) (s : Set (Tableau m N k)))
    (h_span : ∀ (R : Type) [CommRing R] (T : Tableau m N k),
      tableauPoly R id T ∈ Submodule.span R (tableauPoly R id '' (s : Set (Tableau m N k))))
    (h_char : ∀ (M : ℕ) (e : Fin M ≃ m) (x : m → ℂ),
      (∑ T ∈ s, ∏ h : Fin N, ∏ j : Fin (k h), ∏ a : Fin h, x (T h j a)) *
          GL.alternant (x ∘ e) 0 =
        GL.alternant (x ∘ e) fun i ↦ ∑ h ∈ Ioo i N, k h) :
    IsTableauBasis s :=
  ⟨fun R _ ↦ ⟨h_indep R, h_span R⟩, h_char⟩

/-- The standard fillings: the members of a chosen finite set of fillings that satisfies
`IsTableauBasis` as soon as some set does. This is the case for a finite alphabet `m`
(`isTableauBasis_epsilon`). They need not be semistandard tableaux. -/
def BasisTableau (m : Type) [DecidableEq m] (N : ℕ) (k : ℕ → ℕ) : Type :=
  {T : Tableau m N k // T ∈ (Classical.epsilon IsTableauBasis : Finset (Tableau m N k))}
deriving Fintype, DecidableEq

/-- The number of elements of the finite row type n_τ at the place τ. -/
abbrev rankAt : ℕ := Fintype.card (n τ)

/-- The fixed enumeration of the rows of n_τ by 0,…,|n_τ|−1, as an equivalence of n_τ with `Fin`
|n_τ|. -/
abbrev GL.rowEquivFin : n τ ≃ Fin (Fintype.card (n τ)) := Fintype.equivFin (n τ)

/-- The type of families choosing, for each place τ, a filling in the chosen standard set with
rows n_τ, heights below |n_τ| and multiplicities κ_τ. It indexes the basis `nablaBasis` of
`nablaFamily`; the Weyl module over `R` is the dual, `WeylIndexFamily n κ → R` in the dual basis. -/
abbrev WeylIndexFamily : Type := ∀ τ : Φ, BasisTableau (n τ) (rankAt n τ) (κ τ)

/-- The type of families of chosen standard fillings over the places, in the case where the row
type is the same finite type n at every place. -/
abbrev WeylIndex (n : Type) [Fintype n] [DecidableEq n] (κ : Φ → ℕ → ℕ) :
    Type := WeylIndexFamily (fun _ : Φ ↦ n) κ

/-- The module of Borel semi-invariant polynomials in rows (τ,a), coloured by τ, whose weight is
the partition tuple built from κ using heights below |n_τ|. It is the span ∇ of the products of
minors, one for each column of the diagram (`span_fillingPoly`). -/
abbrev nablaFamily : Submodule R (MatrixPoly (Sigma n) R) :=
  nabla R (fst (β := n)) (diagramWeight (rankAt n) κ)

/-- For a family i of chosen standard fillings, the polynomial that is the product over places τ
of the minor product of i_τ in the rows of block τ. -/
def nablaBasis (i : WeylIndexFamily n κ) : MatrixPoly ((τ : Φ) × n τ) R :=
  ∏ τ : Φ, tableauPoly (m := Σ τ : Φ, n τ) R (Sigma.mk τ) (i τ).1

/-- The polynomial product over places τ and h<N_τ of the leading principal h×h minor of the
variables in block τ raised to κ_τ(h). -/
def highestPoly (N : Φ → ℕ) : MatrixPoly ((τ : Φ) × Fin (N τ)) R :=
  ∏ τ : Φ,
    tableauPoly R (Sigma.mk τ) (fun h _ ↦ Fin.castLE h.is_le' : Tableau (Fin (N τ)) (N τ) (κ τ))

/-- For exponents `e : Φ → ℕ`, the product over places τ of the determinant of the variables in
all rows of block τ (fixed enumeration) and the first |n_τ| columns, raised to `e τ`. -/
def detPow : MatrixPoly ((τ : Φ) × n τ) R :=
  ∏ τ : Φ, minor (m := Σ τ : Φ, n τ) R (fun a ↦ ⟨τ, (Fintype.equivFin (n τ)).symm a⟩) ^ e τ

/-- The generic tuple of square matrices: the `(a, b)` entry at `τ` is the variable
`X ⟨τ, a, b⟩`. -/
def GL.genericMatrixAt : Matrix (n τ) (n τ) (MvPolynomial ((τ : Φ) × n τ × n τ) R) :=
  of fun a b ↦ X (R := R) (σ := Σ τ : Φ, n τ × n τ) ⟨τ, a, b⟩

/-- The hook number: the integer ⟨f,f⟩ = f(∂)f(0), where f is the product of the leading
principal h×h minors raised to κ_τ(h), h<N_τ. -/
def hookNumber (N : Φ → ℕ) : ℤ := fockPairing ℤ (highestPoly ℤ κ N) (highestPoly ℤ κ N)

/-- The natural number κ_τ(|n_τ|) if |n_τ| < |n'_τ|, and 0 otherwise, as a function of the place
τ. Under `FitsRanks` and for |n_τ| > 0 it is the length of row number |n_τ|, counted from 1, of the
diagram with κ_τ(h) columns of height h < |n'_τ|. -/
def schurDetExp : ℕ := if rankAt n τ < rankAt n' τ then κ τ (rankAt n τ) else 0

/-- The condition, at every place τ, that |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|:
the diagram with κ_τ(h) columns of height h < |n'_τ| has at most |n_τ| rows. -/
@[grind]
def FitsRanks : Prop :=
  ∀ τ : Φ, rankAt n τ ≤ rankAt n' τ ∧ ∀ h ∈ Ioo (rankAt n τ) (rankAt n' τ), κ τ h = 0

variable {R n n'} (y : (Σ τ : Φ, n τ) × ℕ → R) (α : σ →₀ ℕ) (a : R) (f g : MvPolynomial σ R) (i : σ)
  (F : MvPowerSeries σ R)

/-! ### Substitutions and evaluations -/

/-- For matrices z_τ of size n'_τ×n_τ, the algebra homomorphism f ↦ f(zy) sending variable
y_{(τ,b),i} to Σ_a z_τ(b,a) y_{(τ,a),i}; here `x = (⟨τ, b⟩, i)`. -/
def rowSubst (z : (τ : Φ) → Matrix (n' τ) (n τ) R) :
    MatrixPoly (Σ τ : Φ, n' τ) R →ₐ[R] MatrixPoly (Σ τ : Φ, n τ) R :=
  aeval fun x ↦ ∑ a : n x.fst.fst, z x.fst.fst x.fst.snd a • X (⟨x.fst.fst, a⟩, x.snd)

/-- For maps e_τ from rows to natural numbers, the array over R whose entry at row (τ,a), column
i is 1 if e_τ(a)=i and 0 otherwise. -/
def permArray (e : ∀ τ : Φ, n τ → ℕ) (x : ((τ : Φ) × n τ) × ℕ) : R :=
  if e x.fst.fst x.fst.snd = x.snd then (1 : R) else 0

/-- A numbering of the rows is read as a map to `ℕ`. -/
instance : CoeOut (∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) (∀ τ : Φ, n τ → ℕ) := ⟨(· · ·)⟩

/-- The R-linear map sending a coordinate vector ξ to the polynomial Σ_i ξ_i b_i, where the b_i are
the basis products of minors `New.nablaBasis`. -/
abbrev GL.nablaCombination : (WeylIndexFamily n κ → R) →ₗ[R] MatrixPoly ((τ : Φ) × n τ) R :=
  Fintype.linearCombination R (nablaBasis R n κ)

/-- For square matrices `z τ`, the ring homomorphism from polynomials in variables (τ,a,b) to R
evaluating each variable at the matrix entry z_τ(a,b); here `x = ⟨τ, (a, b)⟩`. -/
abbrev GL.evalMatrix (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    MvPolynomial ((τ : Φ) × n τ × n τ) R →+* R :=
  MvPolynomial.eval (R := R) fun x : Σ τ : Φ, n τ × n τ ↦ z x.fst x.snd.fst x.snd.snd

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] in
@[simp]
lemma GL.genericMatrixAt_map_evalMatrix (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) (τ : Φ) :
    (genericMatrixAt R n τ).map (evalMatrix z) = z τ := by
  ext a b
  simp [genericMatrixAt]

/-- For a polynomial `f` and a power series `F`, the pairing `jet R f F`, that is `f(∂) F (0)`, is
the sum of `f.coeff d * d! * F.coeff d` over the monomials `d` of `f`, where `d!` is the product of
the factorials of the exponents. -/
@[local simp↓ low]
lemma jet_eq_sum :
    jet R f F = ∑ d ∈ f.support, f.coeff d * (d.prod fun (_k : σ) (j : ℕ) ↦ ↑j !) * F.coeff d := by
  simp [jet, Basis.constr_apply]
  -- Both sides are the same sum; the factors of each term are in a different order.
  ac_rfl

/-- The pairing of the monomial `a * X ^ α` with the power series `F` is `a * α! * F.coeff α`,
where `α!` is the product of the factorials of the exponents. -/
lemma jet_monomial :
    jet R (monomial α a) F = a * (α.prod fun (_k : σ) (j : ℕ) ↦ ↑j !) * F.coeff α := by
  classical
  aesop

/-- Raising the exponent at `i` by one multiplies `d!` by `d i + 1`. -/
private lemma prod_factorial_add_single (d : σ →₀ ℕ) (i : σ) :
    ((d + Finsupp.single i 1).prod fun (_k : σ) (j : ℕ) ↦ (j ! : R)) =
      ((d i : R) + 1) * d.prod fun (_k : σ) (j : ℕ) ↦ (j ! : R) := by
  rw [← mul_prod_erase' (d + Finsupp.single i 1) i _ (by simp), ← mul_prod_erase' d i _ (by simp),
    Finsupp.erase_add, Finsupp.erase_single, add_zero, Finsupp.add_apply, Finsupp.single_eq_same,
    factorial_succ]
  push_cast
  ring

/-- For the pairing `jet R f F = f(∂) F (0)` of a polynomial with a power series, multiplication of
`f` by `X i` is adjoint to the derivative of `F` in `X i`. -/
@[local simp↓]
lemma jet_mul_X : jet R (f * X i) F = jet R f (F.pderiv i) := by
  -- The monomials of `f * X i` are those of `f` shifted by `X i`; compare term by term.
  rw [jet_eq_sum, jet_eq_sum, support_mul_X, sum_map]
  refine sum_congr rfl fun x _ ↦ ?_
  -- At the exponent `x + single i 1`: `(x i + 1)! = (x i + 1) * (x i)!` matches the derivative.
  rw [addRightEmbedding_apply, coeff_mul_X, prod_factorial_add_single, F.coeff_pderiv]
  ring

/-- The Fock pairing `⟨a * X ^ α, g⟩` is `α! * a * g.coeff α`, where `α!` is the product of the
factorials of the exponents. -/
lemma fockPairing_monomial :
    fockPairing R (monomial α a) g = α.prod (fun (_k : σ) (j : ℕ) ↦ j !) * (a * g.coeff α) := by
  classical
  simp
  grind

/-- The Fock pairing of a constant `a` with `g` is `a` times the constant term of `g`. -/
lemma fockPairing_C : fockPairing R (C a) g = a * constantCoeff g := by
  classical
  aesop

/-- For the Fock form, multiplication by `X i` is adjoint to the derivative in `X i`. -/
lemma fockPairing_mul_X : fockPairing R (f * X i) g = fockPairing R f (pderiv i g) := by
  simp [MvPowerSeries.pderiv_coe]

/-- The Schur matrix `S_κ(z)` of a family of matrices `z τ` of size `n' τ × n τ`. Let `b` and `b'`
be `nablaBasis` for `n` and `n'`, and let `d` be `schurDetExp n n' κ`. Row `i` holds chosen
coordinates of `b'_i(z y)` in the family `b_j(y) * ∏ τ, det(y_τ) ^ d τ`; see
`sum_schur_smul_eq_rowSubst_of_exists`. The row is unspecified if there are no such coordinates;
they exist under `FitsRanks n n' κ` (`sum_schur_smul_nablaBasis`). It is the map of Weyl modules
induced by `z`; for square `z` it is the restriction of the action on tensors
(`fillingMatrixOver_mul_schur`). -/
def schur (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) :
    Matrix (WeylIndexFamily n' κ) (WeylIndexFamily n κ) R :=
  of (invFun
    (Fintype.linearCombination R fun j ↦ nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) ∘
      rowSubst z ∘ nablaBasis R n' κ)

/-- In the notation of `schur` (`n τ`, `n' τ` the finite row types and `κ τ h` the column counts at
the place `τ`): if `b'_i(z y)` is a linear combination of the products
`b_j(y) * ∏ τ, det(y_τ) ^ d τ`, then row `i` of the Schur matrix gives the coefficients of such a
combination. -/
lemma sum_schur_smul_eq_rowSubst_of_exists (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (i : WeylIndexFamily n' κ)
    (h_coords : ∃ w : WeylIndexFamily n κ → R,
      ∑ j : WeylIndexFamily n κ, w j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
        rowSubst z (nablaBasis R n' κ i)) :
    ∑ j : WeylIndexFamily n κ, schur κ z i j •
      (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
      rowSubst z (nablaBasis R n' κ i) :=
  invFun_eq (f := Fintype.linearCombination R
    fun j ↦ nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) h_coords

/-- For a family i of fillings, a place τ and a row a, the number of entries of the filling i_τ
equal to a. -/
def tableauWeight {κ : Φ → ℕ → ℕ} (i : WeylIndexFamily n κ) (τ : Φ) (a : n τ) : ℕ :=
  ∑ h : Fin (rankAt n τ), ∑ j : Fin (κ τ h), #{s : Fin h | (i τ).val h j s = a}

variable (n)

/-- For an array `y` over `R`, the polynomial `f(yᵀx)` in `x`, where `f` is the product of leading
minors `New.highestPoly`. Block `τ` uses the first `|n_τ|` columns of `y`. It is the pairing of the
tensors of `x` and `y` (`weylKernel_eq_sum_fillingPoly`). -/
def weylKernel : MatrixPoly ((τ : Φ) × n τ) R :=
  rowSubst (fun τ ↦ of fun i a ↦ y (⟨τ, a⟩, i.val)) (highestPoly R κ (rankAt n))

/-- The Gram matrix `G`: chosen integer coefficients of the generic kernel `weylKernel n κ X` in
the products `b_i(x) * b_j(y)`, where `b` is `nablaBasis`. The kernel is first expanded in the
`b_i(x)` with coefficients in `ℤ[y]`, and row `i` expands the `i`-th coefficient in the `b_j(y)`;
see `sum_weylGram_smul_eq_weylKernel_of_exists`. Both expansions exist, and `toPoly_weylEval` states
the resulting identity. It is the matrix of the form on the Weyl module for which the basis tensors
are orthonormal (`fillingMatrix_transpose_mul_self`). -/
def weylGram : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ :=
  of (invFun (GL.nablaCombination (R := ℤ) κ) ∘
    invFun (GL.nablaCombination (R := MatrixPoly (Σ τ : Φ, n τ) ℤ) κ) (weylKernel n κ X))

/-- Let `n τ` be the finite row type and `κ τ h` the number of columns of height `h` at the place
`τ`, let `y` be the array of variables `X` with rows `(τ, a)`, and let `b = nablaBasis`. If `b` is
linearly independent over the polynomial ring `ℤ[y]` and the generic kernel `weylKernel n κ X` is an
integer combination of the products `b_i(x) * b_j(y)`, then `weylGram` gives the coefficients of
such a combination. -/
lemma sum_weylGram_smul_eq_weylKernel_of_exists {Φ : Type} [Fintype Φ] [DecidableEq Φ]
    (n : Φ → Type) [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] (κ : Φ → ℕ → ℕ)
    (h_indep : LinearIndependent (MatrixPoly (Σ τ : Φ, n τ) ℤ)
      (nablaBasis (MatrixPoly (Σ τ : Φ, n τ) ℤ) n κ))
    (h_coords : ∃ G : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ,
      ∑ i : WeylIndexFamily n κ, (∑ j : WeylIndexFamily n κ, G i j • nablaBasis ℤ n κ j) •
        nablaBasis (MatrixPoly (Σ τ : Φ, n τ) ℤ) n κ i = weylKernel n κ X) :
    ∑ i : WeylIndexFamily n κ, (∑ j : WeylIndexFamily n κ, weylGram n κ i j • nablaBasis ℤ n κ j) •
        nablaBasis (MatrixPoly (Σ τ : Φ, n τ) ℤ) n κ i = weylKernel n κ X := by
  obtain ⟨G, hG⟩ := h_coords
  -- By independence the coordinates in the `b_i(x)` are unique, so they are those given by `G`.
  have h_outer : invFun (GL.nablaCombination κ) (weylKernel n κ X) =
      fun i ↦ ∑ j, G i j • nablaBasis ℤ n κ j :=
    h_indep.fintypeLinearCombination_injective <|
      (invFun_eq (f := GL.nablaCombination κ) ⟨_, hG⟩).trans hG.symm
  have h_row (i : WeylIndexFamily n κ) :
      ∑ j, weylGram n κ i j • nablaBasis ℤ n κ j = ∑ j, G i j • nablaBasis ℤ n κ j := by
    rw [weylGram, h_outer]
    exact invFun_eq (f := GL.nablaCombination κ) ⟨G i, rfl⟩
  simp only [h_row, hG]

variable {n} in
/-- The integer Gram matrix `New.weylGram` for the row type n and column counts κ, with its entries
mapped into R. -/
abbrev weylGramOver {κ : Φ → ℕ → ℕ} : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R :=
  (weylGram n κ).map (Int.cast : ℤ → R)

/-- The polynomial of a vector ξ of the Weyl module: Σ_i (Gξ)_i b_i, with G the Gram matrix and b_i
the basis minor products. It is the pairing of the tensor of ξ with the tensor of the variables
(`toPoly_eq_sum_fillingPoly`). -/
def toPoly : (WeylIndexFamily n κ → R) →ₗ[R] MatrixPoly ((τ : Φ) × n τ) R :=
  GL.nablaCombination κ ∘ₗ ((weylGram n κ).map (Int.cast : ℤ → R)).mulVecLin

/-- For an array `y` over `R`, the value `b_i(y)` at `y` of the basis product of minors
`b_i = nablaBasis R n κ i`. The vector `weylEval n κ y` of the Weyl module is the evaluation at `y`;
as a tensor it is the tensor of `y` (`fillingMatrixOver_mulVec_weylEval`). -/
def weylEval (i : WeylIndexFamily n κ) : R := (nablaBasis R n κ i).eval y

variable [Fintype m] (z : Matrix m σ R) {R' : Type _} [CommRing R'] [Fintype σ] [DecidableEq σ]

/-! ### Linear substitutions, symmetric powers and polynomials from coefficients -/

/-- For an m×σ matrix z over R, the R-algebra map from polynomials in variables indexed by σ to
those indexed by m sending X_b to ∑_t z_{tb} X_t. -/
def linSubst : MvPolynomial σ R →ₐ[R] MvPolynomial m R := aeval fun s ↦ ∑ t : m, z t s • X t

/-- The chain rule for a linear substitution: the derivative of `p(zᵀx)` in `x_i` is
`Σ_a z_{ia} (∂p/∂x_a)(zᵀx)`. -/
lemma pderiv_linSubst {σ m R : Type} [CommRing R] [Fintype m] (z : Matrix m σ R) [Fintype σ]
    [DecidableEq σ] (p : MvPolynomial σ R) (i : m) :
    (linSubst z p).pderiv i = ∑ a : σ, z i a • linSubst z (p.pderiv a) := by
  classical
  -- By induction from the variables; the step for `p * X j` is the Leibniz rule.
  induction p using MvPolynomial.induction_on with
  | C r => simp [linSubst]
  | add p q hp hq => simp [hp, hq, sum_add_distrib]
  | mul_X p j hp =>
    have h_X : linSubst z (X j) = ∑ t : m, z t j • X t := by simp [linSubst]
    simp [Derivation.leibniz, hp, h_X, Finset.mul_sum, sum_add_distrib, Pi.single_apply,
      apply_ite, mul_comm, add_comm]

/-- For an `m × σ` matrix `z` over the commutative ring `R`, the substitutions by `z` and by `zᵀ`
(`New.linSubst`) are adjoint for the Fock form `⟨p, q⟩ = p(∂) q (0)`. -/
lemma fockPairing_linSubst {σ m R : Type} [CommRing R] [Fintype m] (z : Matrix m σ R) [Fintype σ]
    [DecidableEq σ] (f : MvPolynomial m R) (g : MvPolynomial σ R) :
    fockPairing R f (linSubst z g) = fockPairing R (linSubst zᵀ f) g := by
  classical
  -- A factor `X i` of `f` moves across the Fock form as `pderiv i` (`fockPairing_mul_X`), and
  -- both sides then agree by the chain rule; for constants only the constant terms matter.
  induction f using MvPolynomial.induction_on generalizing g with
  | C c => simp [linSubst, fockPairing_C, hom_bind₁, -fockPairing]
  | add p q hp hq => simp [hp, hq, -fockPairing]
  | mul_X p i hp =>
    have h_subst : linSubst zᵀ (p * X i) = ∑ a : σ, z i a • (linSubst zᵀ p * X a) := by
      simp [linSubst, univ.mul_sum]
    simp [fockPairing_mul_X, pderiv_linSubst, h_subst, hp, -fockPairing]

variable {n} (a : ℕ) (ψ : R →+* R') (A B : Matrix σ σ R)

variable (σ) in
/-- The exponents of the monomials of degree `a` in variables indexed by `σ`. -/
abbrev Monomials : Type := ↥((univ : Finset σ).finsuppAntidiag a)

omit [DecidableEq σ] in
/-- `linSubst A` substitutes for each variable the linear form of the matching row of `Aᵀ`. -/
lemma linSubst_eq_bind₁ : linSubst A = bind₁ Aᵀ.toMvPolynomial := by
  ext s : 1
  simp [linSubst, Matrix.toMvPolynomial, smul_eq_C_mul, C_mul_X_eq_monomial]

@[simp]
lemma linSubst_one : linSubst 1 f = f := by simp [linSubst_eq_bind₁]

omit [DecidableEq σ] in
lemma linSubst_mul : linSubst (A * B) f = linSubst A (linSubst B f) := by
  simp [linSubst_eq_bind₁, bind₁_bind₁, ← toMvPolynomial_mul]

omit [DecidableEq σ] in
lemma map_linSubst :
    MvPolynomial.map ψ (linSubst A f) = linSubst (A.map ψ) (MvPolynomial.map ψ f) := by
  simp [linSubst, map_bind₁, ← C_mul']

variable {a f} {S : Type _} [Fintype S] [DecidableEq S] (α : Monomials σ a)

lemma Monomials.degree_eq : α.val.degree = a := by
  simpa [degree_eq_sum] using (mem_finsuppAntidiag.mp α.property).left

lemma Monomials.isHomogeneous_linSubst : (linSubst A (monomial α 1)).IsHomogeneous a := by
  rw [linSubst_eq_bind₁, ← aeval_eq_bind₁]
  simpa only [one_mul] using
    (isHomogeneous_monomial (1 : R) α.degree_eq).aeval _ Aᵀ.toMvPolynomial_isHomogeneous

/-- A polynomial `f`, homogeneous of degree `a` in finitely many variables, is the sum of its terms
`f.coeff β • X ^ β` over the exponents `β` of degree `a`. -/
lemma sum_monomials_eq_of_isHomogeneous (hf : f.IsHomogeneous a) :
    ∑ β : Monomials σ a, f.coeff β • monomial β 1 = f := by
  ext d
  -- Only the term `β = d` contributes; if `d` has another degree, `f.coeff d = 0`.
  simpa [coeff_sum, eq_comm, sum_attach _ fun β ↦ ite _ (f.coeff β) 0, ← degree_eq_sum] using
    hf.coeff_eq_zero (d := d)

/-- The a-th symmetric power: the homomorphism sending a square matrix A to the matrix, in the
monomial basis, of `New.linSubst` A on forms of degree a. -/
def symPowMatrix (a : ℕ) : Matrix σ σ R →* Matrix (Monomials σ a) (Monomials σ a) R where
  toFun A := of fun β α ↦ (linSubst A (monomial α.1 1)).coeff β.1
  map_one' := by simp [eq_comm, one_apply, ← ext_iff]
  map_mul' A B := by
    ext β α
    -- Expand `linSubst B (monomial α 1)` in the monomials of degree `a`, then apply `linSubst A`.
    show (linSubst (A * B) (monomial α.1 1)).coeff β.1 = _
    rw [linSubst_mul, ← sum_monomials_eq_of_isHomogeneous (α.isHomogeneous_linSubst B)]
    simp [mul_comm, Matrix.mul_apply]

/-- For a family `β` of degree-`a` exponent vectors indexed by `S`, the single exponent vector on
the variables `(b, s)` whose value is `β_s(b)`. -/
def exponentOf : (S → Monomials σ a) ↪ σ × S →₀ ℕ where
  toFun β := equivFunOnFinite.symm fun x ↦ (β x.2).1 x.1
  inj' :=
    id fun β β' h ↦ by
      ext s t
      exact DFunLike.congr_fun h (t, s)

/-- For a coefficient function F on families β of degree-a exponents, the polynomial ∑_β F(β)
x^β in the variables (b,s). -/
def polyOfCoeffs : ((S → Monomials σ a) → R) →ₗ[R] MvPolynomial (σ × S) R :=
  ∑ β : S → Monomials σ a, monomial (R := R) (exponentOf β) ∘ₗ LinearMap.proj β

lemma symPowMatrix_map : symPowMatrix a (A.map ψ) = (symPowMatrix a A).map ψ := by
  simp [symPowMatrix, ← coeff_map, map_linSubst, ← ext_iff]

end New

end Defs

/-!
## Semi-invariants, substitution, the Fock pairing and change of coefficients

* `New.diagramWeight_apply`: the weight in closed form.
* The pairings and the polynomials `New.nablaBasis`, `New.highestPoly`, `New.detPow` commute with
  change of the coefficient ring.
-/

section Nabla

open Finset MvPolynomial Matrix Sigma SetLike

namespace New

variable {σ : Type} {Φ m : Type} {R S : Type}
  {l : Φ × ℕ →₀ ℕ} [CommRing R] [CommRing S]
  {c : m → Φ} (φ : R →+* S) (p q : MvPolynomial σ R) {n n' : Φ → Type _}
  {n'' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, Fintype (n' τ)]
  (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) {f : MatrixPoly m R}

/-! ### Semi-invariants -/

/-- `f` lies in `New.nabla R c l` (it is a semi-invariant of weight `l` for the row colouring `c`)
iff for every `R`-algebra `S` and all arrays `b`, `y` over `S` we have
`f(y b) = ∏ b(τ, i, i) ^ l(τ, i) · f(y)`. Here `y b` is `New.borelMul c b y`, the array with
`(a, j)` entry `Σ_{i ≤ j} y(a, i) b(c a, i, j)`, so only the upper triangular part of `b` is
used. -/
lemma mem_nabla :
    f ∈ nabla R c l ↔
      ∀ (S : Type) [CommRing S] [Algebra R S] (b : Φ × ℕ × ℕ → S) (y : m × ℕ → S),
        aeval (borelMul c b y) f =
          (l.prod fun (p : Φ × ℕ) (k : ℕ) ↦ b (p.fst, p.snd, p.snd) ^ k) * aeval y f := by
  -- By definition, membership is this identity for the generic arrays, whose entries are variables.
  simp only [nabla, LinearMap.mem_eqLocus, AlgHom.toLinearMap_apply, LinearMap.smul_apply]
  constructor
  · intro h S _ _ b y
    -- Specialise both families of variables, to `b` and to `y`, by the evaluation `ψ`.
    let ψ : MatrixPoly m (MvPolynomial (Φ × ℕ × ℕ) R) →ₐ[R] S := aevalTower (aeval b) y
    simpa [ψ, comp_aeval_apply, borelMul.eq_unfold, smul_eq_C_mul, map_finsuppProd] using
      congr_arg ψ h
  · intro h
    -- The identity for the generic arrays `C ∘ X` and `X` is membership.
    simpa [smul_eq_C_mul, map_finsuppProd] using
      h (MatrixPoly m (MvPolynomial (Φ × ℕ × ℕ) R)) (C ∘ X) X

/-- Semi-invariants multiply, and their weights add. -/
instance : SetLike.GradedMonoid (nabla R c) where
  one_mem := by simp [mem_nabla]
  mul_mem l₁ l₂ f₁ f₂ hf₁ hf₂ := by
    rw [mem_nabla] at hf₁ hf₂ ⊢
    intro S _ _ b y
    simp [hf₁, hf₂, Finsupp.prod_add_index', mul_mul_mul_comm, pow_add]

/-- A minor on `h` rows of colour `τ` and the first `h` columns is a semi-invariant of weight `1`
at `(τ, 0), …, (τ, h - 1)` and `0` elsewhere. -/
lemma minor_mem_nabla {h : ℕ} {τ : Φ} {I : Fin h → m} (hI : ∀ s : Fin h, c (I s) = τ) :
    minor R I ∈ nabla R c (∑ i ∈ range h, Finsupp.single (τ, i) 1) := by
  -- The chosen `h × h` block of `borelMul c b y` is `Y * B`, with `Y` the block of `y` and `B`
  -- upper triangular, so its determinant is the minor of `y` times the diagonal entries of `B`.
  rw [mem_nabla]
  intro S _ _ b y
  let Y : Matrix (Fin h) (Fin h) S := of fun s t ↦ y (I s, t)
  let B : Matrix (Fin h) (Fin h) S := of fun s t ↦ if s ≤ t then b (τ, s, t) else 0
  have h_block : (of fun s t : Fin h ↦ borelMul c b y (I s, t)) = Y * B := by
    ext s t
    simp [Y, B, hI, sum_ite, filter_ge_eq_Iic, Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic,
      borelMul, Matrix.mul_apply]
  have hB_upper : B.IsUpperTriangular := fun s t h_lt ↦ ite_eq_right h_lt.not_ge
  have hB_det : B.det = ∏ i ∈ range h, b (τ, i, i) := by
    rw [det_of_isUpperTriangular hB_upper, prod_range]
    simp [B]
  have h_minor (y' : m × ℕ → S) :
      aeval y' (minor R I) = (of fun s t : Fin h ↦ y' (I s, t)).det := by
    simp [minor, det_apply]
  have h_weight : ((∑ i ∈ range h, Finsupp.single (τ, i) 1).prod
      fun (x : Φ × ℕ) (k : ℕ) ↦ b (x.fst, x.snd, x.snd) ^ k) = ∏ i ∈ range h, b (τ, i, i) := by
    simp [← Finsupp.prod_finsetSum_index, pow_add]
  rw [h_weight]
  calc aeval (borelMul c b y) (minor R I)
      = (of fun s t : Fin h ↦ borelMul c b y (I s, t)).det := h_minor _
    _ = (∏ i ∈ range h, b (τ, i, i)) * Y.det := by rw [h_block, det_mul, hB_det, mul_comm]
    _ = (∏ i ∈ range h, b (τ, i, i)) * aeval y (minor R I) := by rw [h_minor]

omit [∀ τ : Φ, Fintype (n' τ)] in
/-- Colour the row `(τ, a)` by `τ` (the colouring `fst`). If `f` is a Borel semi-invariant of
weight `l` in the rows `(τ, b)`, `b : n' τ`, then its substitution `f ↦ f(z y)` by the matrices
`z τ` of size `n' τ × n τ` (`New.rowSubst`) is a Borel semi-invariant of the same weight in the
rows `(τ, a)`, `a : n τ`. -/
lemma rowSubst_mem_nabla {f : MatrixPoly ((τ : Φ) × n' τ) R} (hf : f ∈ nabla R fst l) :
    rowSubst z f ∈ nabla R fst l := by
  rw [mem_nabla] at hf ⊢
  intro S _ _ b y
  -- `zy y'` is the array `y'` with its rows combined by `z`; `f(z y)` at `y'` is `f` at `zy y'`.
  let zy (y' : ((τ : Φ) × n τ) × ℕ → S) (x : ((τ : Φ) × n' τ) × ℕ) : S :=
    ∑ a : n x.fst.fst, z x.fst.fst x.fst.snd a • y' (⟨x.fst.fst, a⟩, x.snd)
  have h_subst (y' : ((τ : Φ) × n τ) × ℕ → S) : aeval y' (rowSubst z f) = aeval (zy y') f := by
    simp [zy, rowSubst, aeval_bind₁, Algebra.smul_def]
  -- `z` combines rows of one colour, so it commutes with the right multiplication `borelMul`.
  have h_comm : zy (borelMul fst b y) = borelMul fst b (zy y) := by
    ext x
    simp [zy, borelMul, smul_sum, sum_mul, sum_comm (γ := n _)]
  rw [h_subst, h_comm, hf, h_subst]

/-! ### Substitution and the Fock pairing -/

/-- Substituting by `z'` (from the rows `n'' τ` to the rows `n' τ`) and then by `z` (to the rows
`n τ`) is substituting by the products `z' τ * z τ`. -/
lemma rowSubst_rowSubst (z' : (τ : Φ) → Matrix (n'' τ) (n' τ) R)
    (f : MatrixPoly ((τ : Φ) × n'' τ) R) :
    rowSubst z (rowSubst (n' := n'') z' f) = rowSubst (fun τ : Φ ↦ z' τ * z τ) f := by
  simp [bind₁_bind₁, mul_smul, sum_smul, sum_comm (γ := n _), rowSubst, smul_sum, Matrix.mul_apply]

@[simp]
lemma rowSubst_one [∀ τ : Φ, DecidableEq (n τ)] (f : MatrixPoly (Sigma n) R) :
    rowSubst (fun τ : Φ ↦ (1 : Matrix (n τ) (n τ) R)) f = f := by
  simp [rowSubst, Matrix.one_apply]

/-- The Fock pairing `⟨p, q⟩` is the sum, over the monomials `d` of `p`, of
`p.coeff d * d! * q.coeff d`, where `d!` is the product of the factorials of the exponents. -/
lemma fockPairing_eq_sum : fockPairing R p q =
    ∑ d ∈ p.support, p.coeff d * (d.prod fun (_k : σ) (j : ℕ) ↦ (j.factorial : R)) * q.coeff d := by
  simp [fockPairing, jet_eq_sum]

/-- The Fock pairing is symmetric. -/
lemma fockPairing_comm : fockPairing R p q = fockPairing R q p := by
  -- Both sides are sums of `p.coeff d * d! * q.coeff d`; the terms outside the common support
  -- vanish.
  rw [fockPairing_eq_sum, fockPairing_eq_sum]
  exact sum_congr_of_eq_on_inter (by simp +contextual) (by simp +contextual) fun d _ _ ↦ by ring

lemma map_jet (F : MvPowerSeries σ R) :
    φ (jet R p F) = jet S (MvPolynomial.map φ p) (MvPowerSeries.map φ F) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a => simp [jet_monomial, map_finsuppProd]
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]

/-- The Fock pairing commutes with a change of coefficients along a ring homomorphism `φ`. -/
lemma map_fockPairing :
    φ (fockPairing R p q) = fockPairing S (MvPolynomial.map φ p) (MvPolynomial.map φ q) := by
  -- Reading `q` as a power series commutes with `map φ`.
  have h_coe : MvPowerSeries.map φ (q : MvPowerSeries σ R) = MvPolynomial.map φ q := by
    ext d
    simp [coeff_map]
  simp [fockPairing, map_jet, h_coe]

/-- The adjoint of substitution by `z` for the Fock pairing is substitution by the transposes. -/
lemma fockPairing_rowSubst [∀ τ : Φ, DecidableEq (n τ)] (p : MatrixPoly ((τ : Φ) × n' τ) R) :
    ∀ q : MvPolynomial (((τ : Φ) × n τ) × ℕ) R,
      fockPairing R (rowSubst z p) q = fockPairing R p (rowSubst (fun τ : Φ ↦ (z τ)ᵀ) q) := by
  classical
  set w : MatrixPoly ((τ : Φ) × n τ) R →ₐ[R] MatrixPoly ((τ : Φ) × n' τ) R :=
    rowSubst fun τ ↦ (z τ)ᵀ
  -- The chain rule for the transposed substitution `w`, by induction on `q` (Leibniz rule).
  have h_chain (q : MatrixPoly ((τ : Φ) × n τ) R) (τ : Φ) (b : n' τ) (k : ℕ) :
      (w q).pderiv (⟨τ, b⟩, k) = ∑ a : n τ, z τ b a • w (q.pderiv (⟨τ, a⟩, k)) := by
    induction q using MvPolynomial.induction_on with
    | C a => simp [w, rowSubst]
    | add q₁ q₂ h₁ h₂ => simp [h₁, h₂, sum_add_distrib, smul_add]
    | mul_X q j h_q =>
      -- The Leibniz rule for `w q * w (X j)`; the derivative of `w (X j)` is an entry of `z`.
      obtain ⟨⟨τ', a'⟩, k'⟩ := j
      have h_X : w (X (⟨τ', a'⟩, k')) = ∑ d : n' τ', z τ' d a' • X (⟨τ', d⟩, k') := by
        simp [w, rowSubst]
      simp [h_q, mul_sum (ι := n _), apply_ite, sum_add_distrib, Pi.single_apply, smul_add, h_X]
      -- Both sides are `z τ b a' • w q` if `τ' = τ` and `k' = k`, and `0` otherwise; `aesop`
      -- matches the dependent pairs.
      show (w q * ∑ x : n' τ', if (τ' = τ ∧ x ≍ b) ∧ k' = k then z τ' x a' • 1 else 0) =
          ∑ x : n τ, if (τ' = τ ∧ a' ≍ x) ∧ k' = k then z τ b x • w q else 0
      aesop (add simp ite_and)
  -- Induction on `p`: multiplication by a variable is adjoint to the partial derivative.
  induction p using MvPolynomial.induction_on with
  | C a => simp [w, fockPairing_C, hom_bind₁, rowSubst]
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p j h_p =>
    intro q
    obtain ⟨⟨τ, b⟩, k⟩ := j
    -- `rowSubst z (X j)` is a combination of variables, each of which moves across as `pderiv`.
    have h_X : rowSubst z (X (⟨τ, b⟩, k)) = ∑ a : n τ, z τ b a • X (⟨τ, a⟩, k) := by
      simp [rowSubst]
    simp [fockPairing_mul_X, h_chain, h_X, mul_sum, h_p]

variable [Fintype Φ] {N : Φ → ℕ} {κ κ' : Φ → ℕ → ℕ} {p}

/-- Over a star-ordered domain `R`, `⟨p̄, p⟩ > 0` for every nonzero polynomial `p`, where `p̄`
applies `star` to each coefficient. -/
lemma fockPairing_star_self_pos [PartialOrder R] [StarRing R] [StarOrderedRing R] [IsDomain R]
    (hp : p ≠ 0) :
    0 < fockPairing R (MvPolynomial.map (starRingEnd R) p) p := by
  -- The value is `∑ d, p.coeff d * d! * star (p.coeff d)` over the nonempty support of `p`.
  rw [fockPairing_comm, fockPairing_eq_sum]
  refine sum_pos (fun d hd ↦ ?_) (support_nonempty.mpr hp)
  rw [coeff_map, starRingEnd_apply]
  exact star_right_conjugate_pos (by simp [Finsupp.prod, prod_pos, Nat.factorial_pos])
    (isRegular_iff_ne_zero.mpr (mem_support_iff.mp hd))

/-! ### The weight, and change of coefficients -/

/-- The weight at `(τ, i)` is the number `∑ i < h < N τ, κ τ h` of columns of colour `τ` higher
than `i`. -/
lemma diagramWeight_apply (τ : Φ) (i : ℕ) : diagramWeight N κ (τ, i) = (Ioo i (N τ)).sum (κ τ) := by
  classical
  -- Only the heights `h` at the place `τ` with `i < h` count.
  have h_eval : diagramWeight N κ (τ, i) = ∑ h ∈ range (N τ), if i < h then κ τ h else 0 := by
    simp [Finsupp.single_apply, diagramWeight, smul_sum, ite_and]
  rw [h_eval, ← sum_filter, show (range (N τ)).filter (fun h ↦ i < h) = Ioo i (N τ) by grind]

lemma diagramWeight_add : diagramWeight N (κ + κ') = diagramWeight N κ + diagramWeight N κ' := by
  simp [diagramWeight, smul_sum, sum_add_distrib]

@[simp]
lemma map_nablaBasis [∀ τ : Φ, DecidableEq (n τ)] (i : WeylIndexFamily n κ) :
    MvPolynomial.map φ (nablaBasis R n κ i) = nablaBasis S n κ i := by
  simp [nablaBasis, tableauPoly, minor, det_apply]

@[simp]
lemma map_highestPoly : MvPolynomial.map φ (highestPoly R κ N) = highestPoly S κ N := by
  simp [highestPoly, tableauPoly, minor, det_apply]

@[simp]
lemma map_detPow (e : Φ → ℕ) : MvPolynomial.map φ (detPow R n e) = detPow S n e := by
  simp [detPow, minor, det_apply]

@[simp]
lemma detPow_zero : detPow R n 0 = 1 := by simp [detPow]

end New

end Nabla

end
