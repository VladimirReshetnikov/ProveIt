# Independent review: logarithmic interpolation for the line relation

## Verdict

**The proposed theorem is correct as stated**, including for nonnormal and nondiagonalizable `T`, provided the two systems use the same positive real parameters `d,c` and the test operator `A` commutes with both `T` and its Hilbert-space adjoint. No powers of `A` are needed in the moment comparison. Interpolation needs values only, not derivative data at repeated eigenvalues.

There is a concrete simplification beyond the full moment hypothesis: if the union of the distinct spectra has `r` elements, equality of the positive mixed moments for `m=1,...,r` suffices. The safe source port may continue using the already available identities for every positive integer `m`.

This is an independent mathematical stress test of the candidate, not a Lean verification and not a claim of historical novelty.

## 1. Precise statement and proof

Let `V` be a finite-dimensional complex Hilbert space. Let `T,A,e` be endomorphisms and let `d,c` be positive real numbers. Suppose

\[
 e^2=e,\qquad TT^*=d(I+ce),\qquad AT=TA,\qquad AT^*=T^*A.
\]

For each nonzero complex number define

\[
 F_{d,c}(z)=\frac{\log(|z|^2/d)}{\log(1+c)}.
\]

For every complex polynomial `p` whose values agree with `F_{d,c}` on the distinct eigenvalues of `T`,

\[
 \operatorname{tr}(Ae)=\operatorname{tr}(A p(T)).
\]

### Preliminary consequences

Taking adjoints in the line relation shows that `e=e*`, because `d,c` are nonzero real scalars. Thus `e` is an orthogonal projection. The eigenvalues of `TT*` are `d` and `d(1+c)`, with the appropriate zero multiplicities if `e=0` or `e=I`; both are positive. Therefore `T` is invertible and its eigenvalues are nonzero. The denominator `log(1+c)` is positive.

The relations also imply that `A` commutes with `e`. Taking adjoints of both commutation hypotheses shows that `A*` commutes with both `T` and `T*`. Consequently the Hermitian operators

\[
 B=(A+A^*)/2,\qquad C=(A-A^*)/(2i)
\]

commute with `T,T*` and `e`.

### A selfadjoint test operator

First let `B=B*` commute with `T,T*`. Decompose `V` orthogonally into the eigenspaces `W_b` of `B`. Each eigenspace is preserved by `T` and `T*`; it is therefore a reducing subspace. It is also preserved by `e`, either from the line relation or direct commutation.

The restrictions satisfy the same relation, with `T|W_b` invertible and the restricted adjoint equal to `(T|W_b)*`. Put `n_b=dim W_b` and `r_b=rank(e|W_b)`. Determinants give

\[
 |\det(T|W_b)|^2=d^{n_b}(1+c)^{r_b}.
\]

If `lambda_j` are the eigenvalues of the restricted `T`, counted with algebraic multiplicity, then

\[
 r_b=\sum_j F_{d,c}(\lambda_j).
\]

Every such eigenvalue belongs to the spectrum of the full `T`. Thus

\[
 \operatorname{tr}(p(T)|W_b)=\sum_jp(\lambda_j)=r_b.
\]

The polynomial trace formula is valid without diagonalizability. It follows from triangularization, or from the usual characteristic-polynomial eigenvalue/trace identities. Multiplying by the scalar `b` and summing over the orthogonal eigenspace decomposition proves

\[
 \operatorname{tr}(Be)=\operatorname{tr}(B p(T)).
\]

Apply this result separately to `B` and `C` above. Trace linearity and `A=B+iC` give the claimed identity for arbitrary `A`.

### Why repeated roots need no Hermite interpolation

Trace of a polynomial depends on polynomial values at eigenvalues with algebraic multiplicities. Nilpotent Jordan contributions have trace zero. More generally, if two polynomials agree on the distinct spectrum, their difference evaluated at `T` is nilpotent. When `A` commutes with `T`, it also commutes with this nilpotent operator, so their product is nilpotent and has trace zero. Therefore even the weighted polynomial trace is insensitive to missing derivative data.

## 2. Transfer using positive moments only

For a second system `V',T',A',e'` satisfying the same hypotheses with the **same** `d,c`, let `Sigma` be the union of the distinct spectra. It is finite and excludes zero.

Interpolate the function `lambda -> F_{d,c}(lambda)/lambda` on `Sigma`, obtaining a polynomial `q` of degree at most `r-1`, where `r=|Sigma|`. Then put `p(X)=X q(X)`. This has `p(0)=0`, degree at most `r`, and the required values on both spectra.

Write `p(X)=sum_{m=1}^r a_m X^m`. If

\[
 \operatorname{tr}(A T^m)=\operatorname{tr}(A'T'^m)
 \quad (1\le m\le r),
\]

then the trace identities above imply

\[
 \operatorname{tr}(Ae)=\operatorname{tr}(A'e').
\]

No hypothesis about `tr(A^k T^m)` for `k>1`, no equality of dimensions, and no zeroth moment is required. The degree bound `r <= dim V + dim V'` gives a dimension-based finite bound if desired. A source theorem that supplies every positive `m` can be used unchanged.

If both spaces have dimension zero, take `p=0`. If only one does, interpolate on the other spectrum. Empty determinants equal one and empty traces equal zero, so the proof has no mathematical exceptional case beyond ordinary API bookkeeping.

## 3. Adjoint commutation is essential

Take the rational matrices

\[
 T=\begin{pmatrix}1&3/2\\0&1\end{pmatrix},\quad
 e=\begin{pmatrix}4/5&2/5\\2/5&1/5\end{pmatrix},\quad
 d=1/4,\quad c=15.
\]

Direct multiplication gives `e^2=e=e*` and `TT*=d(I+ce)`. The operator `T` is nonnormal and has one eigenvalue `1` of algebraic multiplicity two. Here

\[
 F_{d,c}(1)=\frac{\log 4}{\log16}=\frac12,
 \qquad p(X)=X/2
\]

is an admissible polynomial with zero constant coefficient.

Let

\[
 A=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
\]

Then `A` commutes with `T`, but not with `T*`, and

\[
 \operatorname{tr}(Ae)=2/5,\qquad
 \operatorname{tr}(A p(T))=0.
\]

Thus dropping adjoint commutation is invalid. It also illustrates why `e=p(T)` is **not** the theorem: even with `A=I`, these two matrices are unequal, while their traces coincide.

An equivalent source-friendly hypothesis is commutation of `A` with `T` and `e`. Indeed, since `T` is invertible,

\[
 T^*=dT^{-1}(I+ce).
\]

Hence commutation with `T,e` implies commutation with `T*`; the converse follows from the line relation. If the source already proves that `A` preserves both the cuspidal subspace and its orthogonal complement, the corresponding projection commutation may be the shorter adapter.

## 4. A single moment is not enough

Set

\[
 T=\operatorname{diag}(1,2),\quad
 e=\operatorname{diag}(0,1),\quad d=1,\quad c=3,
 \quad A=\operatorname{diag}(-2,1).
\]

All commutation assumptions hold, but

\[
 \operatorname{tr}(AT)=0,\qquad \operatorname{tr}(Ae)=1.
\]

Comparison with `A'=0` shows that equality of only the first positive moment is insufficient. The second positive moment is `2`; interpolation uses `p(X)=(X^2-X)/2`.

Even adding the zeroth moment does not rescue this shortcut in general. For

\[
 T=\operatorname{diag}(1,2,-2),\quad
 e=\operatorname{diag}(0,1,1),\quad A=\operatorname{diag}(-4,3,1),
\]

both `tr(A)` and `tr(AT)` are zero, but `tr(Ae)=4`. The valid zero-constant interpolant is

\[
 p(X)=X^3/12+X^2/4-X/3.
\]

The new argument removes powers of the **test operator** `A`; it does not remove the required powers of the **line operator** `T`.

## 5. Further pitfalls and formalization advice

- **Parameters must match.** In dimension one, `T=1` is compatible with `d=1,c=3,e=0`, and also with `d=1/4,c=3,e=1`. Every positive moment for `A=1` agrees, but the projection traces differ. A common function `F_{d,c}` is essential.
- **Projection idempotence is essential.** The determinant identity gives a sum of `log(1+c alpha)` for arbitrary eigenvalues `alpha` of a general selfadjoint `e`; this is not `tr(e) log(1+c)` unless the idempotent structure is present.
- **Do not use a spectral theorem for `T`.** It need not be normal. Apply the spectral theorem to the Hermitian parts of `A` only. Ordinary characteristic-polynomial trace/determinant identities suffice for `T`.
- **Do not assert an operator polynomial formula for `e`.** The result is equality of weighted traces against the joint commutant of `T,T*`.
- **Complex interpolation coefficients are allowed.** The finite function `lambda -> log(|lambda|^2/d)` is not holomorphic as a global function. Nothing requires it to be: only interpolation on a finite set is used.
- **No logarithm branch of a complex determinant is used.** All logarithms are real logarithms of positive reals. The equality `log |det T|^2=sum log |lambda|^2` follows from products of positive norms.
- **Isolate the lemma from automorphic input.** An abstract linear-algebra theorem with this exact line relation can replace the current reconstruction machinery without changing the existing geometric trace formulas.
- **Prefer the existing all-positive-moment contract for the first port.** The finite degree refinement is mathematically available, but proving a cardinality bound is optional and may add Lean overhead without shortening the main consumer.
- **A shorter alternative proof exists by induction on invariant eigenspaces of `A`.** The eigenspaces are reducing for `T,T*`; the off-diagonal part of `A` contributes no trace against the resulting block-diagonal `e,p(T)`. The Hermitian-parts proof is conceptually cleaner and probably fits existing selfadjoint spectral APIs better.

## 6. Executable evidence

`check_trace_transfer.py` uses SymPy 1.14.0 and passed **107 assertions in 11 examples**. It checks:

1. The rational Jordan example, its line relation, nonnormality, repeated eigenvalue and the failure of `e=p(T)`.
2. Three nonscalar test operators of the form `M tensor I` mixing two copies of the Jordan block. They commute with both line operators, and both weighted traces equal `tr(M)`; normality of `A` is not assumed.
3. The exact counterexample when adjoint commutation is removed.
4. Failure of first-moment-only, and zeroth-plus-first-moment-only, shortcuts.
5. A nonnormal matrix with distinct complex eigenvalues `(9 +/- i sqrt(119))/10`, each of squared modulus `2`, using an exact rational interpolant.
6. A nonnormal matrix with distinct positive real eigenvalues and nonconstant logarithmic interpolation values. Matrix identities are exact; the logarithmic conclusion is a separately labelled 80-decimal numerical regression.
7. Failure when the two systems use different `d` values.
8. The empty determinant and trace conventions.

Run:

```sh
python3 check_trace_transfer.py --output trace_transfer_check_results.json
```

The proof above establishes the universal result. These finite examples are safeguards against invalid strengthenings and implementation mistakes; they do not replace a Lean proof or certify the full GRH development.
