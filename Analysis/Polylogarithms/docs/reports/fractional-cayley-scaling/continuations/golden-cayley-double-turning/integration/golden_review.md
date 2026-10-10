# Independent mathematical review of the golden certificates

## Verdict and scope

The argument in `sections/03_golden.tex` proves the two displayed golden weight-five evaluations, their ordinary polylogarithm companions at weights one through four, and the stated canonical index-12, index-20, and index-24 normalizations. I found no unresolved mathematical gap. The section correctly makes no claim of upward continuation to weights six through nine or of historical priority.

This review examined the analytic argument, the exact algorithm in `code/certify_golden_ladders.py`, and the data in `data/golden_rational_certificates.json`. It independently checked the printed certificate tables against the JSON and checked the canonical coefficient vectors and correction terms using rational arithmetic. It did not repeat numerical diagnostics. The full polynomial factorization and tensor replay remain the computational certificate supplied with the proof; they are finite exact algebra, not integer-relation or numerical evidence.

## Analytic checks

Writing (L=\log|x|), (M=\log|1-x|), and

\[
F_n(x)=\sum_{r=0}^{n-1}\frac{(-L)^r}{r!}\operatorname{Re}\operatorname{Li}_{n-r}(x),
\]

termwise differentiation gives

\[
dF_n=\frac{(-1)^n}{(n-1)!}L^{n-1}\,dM.
\]

The definition in the section satisfies

\[
\mathcal R_n=F_n+\frac{(-1)^{n-1}}{n!}L^{n-1}M,
\qquad
d\mathcal R_n=\frac{(-1)^n(n-1)}{n!}
L^{n-2}(L\,dM-M\,dL).
\]

These signs and factorials are correct, including at weight two. Under inversion, the substitutions ((L,M)\mapsto(-L,M-L)) give the stated parity and the constants fixed at (x=1) and (x=-1). Duplication follows from ordinary polylogarithm duplication with (\log(x^2)=2L); the exceptional final term has the required scaling too.

The principal boundary values on the real cut have well-defined real parts. Their real derivatives obey the relation used in the proof on each interval avoiding zero and one. At (x=1), the monologarithm's singularity is multiplied by a positive power of (\log|x|), so it tends to zero. The remaining terms have the stated continuous limits. At (x=0), powers of (\log|x|) multiplied by the vanishing polylogarithms also tend to zero.

Every argument in the finite tables is nonconstant and has no zero or pole on (0<t<1). All exponents of (t) are nonnegative. Thus there are only finitely many crossings of (f(t)=1); continuity joins the locally constant sums across them. The endpoint calculation as (t\to0^+\) is valid even when the limiting value (+1) is approached from above. No differentiation of an identity at an isolated algebraic number is used.

## Tensor and finite-coordinate checks

The tensor lives in the full rationalized multiplicative group of (\mathbb Q(t)), with signs removed as torsion. Rational primes must remain in this group. The verifier retains numerator and denominator contents, normalizes each polynomial to a primitive integer polynomial of positive leading coefficient, and accounts for the resulting scalar at its multiplicity. In particular, the prime-2 coordinate in (1-f) is retained. I found no scalar-content loss or sign inconsistency in this implementation.

The first tensor factors lie in the three-dimensional span of (t,1-t,1+t); the wedge can use the full factor alphabet. The implementation uses distinct index sets for these two roles. This is legitimate: checking each sorted prefix checks one representative of every equal coordinate under permutation of the first slots. Missing multinomial factors cannot affect a zero assertion. The wedge coefficients have the required antisymmetric sign.

Contracting designated first tensor slots with the linear functional taking values (1,2,-1) on (t,1-t,1+t) gives precisely (k^{5-n}\beta_n[f]), where (k=a+2b-c). There is no extra combinatorial factor. Logarithmic evaluation of the remaining tensor produces the derivative identity above. The program also verifies the four descended equations directly.

An independent exact transcription check found that all 66 rows of the combined printed table agree with the JSON, giving respectively 58 and 60 nonzero coefficients. The printed twelve-row index-12 certificate agrees as well. All rows meet the nonconstant-argument and nonnegative-endpoint-exponent hypotheses.

## Constants, reconstruction, and canonical normalization

The specialization algorithm correctly applies even-weight inversion constants before negative-argument duplication, treats exponent zero as a constant, and uses (0^0=1) only for the weight-five coefficient. The elementary factorizations for (1-\rho^j) include the correct prime logarithms, including the (5^{3/2}11) content at (j=20). Their cancellation yields the claimed weight-one coefficients.

The triangular system for the ordinary functions is invertible, with solution

\[
S_m=\frac{a\lambda^m}{m!}
 +\sum_{r=2}^m q_r\zeta(r)\frac{\lambda^{m-r}}{(m-r)!}.
\]

Independent substitution confirms both the binomial cancellation of lower (q_r) terms and the cancellation of the (a) term in the modified Rogers combination. The resulting two weight-five evaluations have the stated signs after (\lambda=-\log\phi).

The canonical definitions are now present in the standalone section. Exact rational recombination confirms their complete coefficient vectors and correction terms. For index 24, the raw third vector plus (64/3) times the first vector, divided by (-15\cdot24^4), gives the canonical vector at every weight under consideration. The correction coefficients cancel all terms at weights one through four, while the weight-five values are

\[
L_{12}(5)=\frac{67}{6912}\zeta(5),\qquad
L_{20}(5)=\frac{201}{10000}\zeta(5),\qquad
L_{24}(5)=-\frac{1541}{110592}\zeta(5).
\]

No further correction is required by this review. The proof is a conventional analytic proof with a finite exact algebraic certificate; it is not a formal proof-assistant verification.
