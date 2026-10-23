# Additional review of the twelve-positive ordinary-root merger

The full ordered argument in positive/PROOF.md was reviewed separately
from its implementation. No local mathematical gap was found.

The decisive steps are valid in the needed order:

* The formal four-factor norm identity is unconditional. Eliminating rho
  gives C0+4dx(2dQ-M)b, b²=r; its final norm is exactly the delivered
  C0²-16d²x²r(2dQ-M)². Thus the modulo16 guard does not presuppose that
  Q or A are squares. The main residual is also square modulo16 since
  U=4q^4. Their unit-product guard really forces both residuals to zero
  and Nt=1, rather than admitting negative unit branches.
* The explicit shift f=f0+1 excludes Q=0 and d=0 before saturation or
  denominator clearing. V=0 is excluded from the norm using positivity
  of each real quadratic factor, before the estimate y>=1 is used.
* ell-k>a+2 suffices for the two strict weight inequalities. Consequently
  the largest irrational square class cannot cancel in the rational
  carrier sum, even when several radicands have the same square class.
  This is not an assumption of independent Galois sign changes.
* Once sqrt(Q) and tau are integers and y rational, Pell saturation
  makes y integral; the original carrier identity then makes sqrt(Q)/c²
  integral. No unsupported division of Delta in the ordinary strong
  equation is used.
* The U congruence and first Pell equation give an early lower index
  bound before ordinary strong rank is invoked. Only after p=R is
  recovered is full divisibility used to restore h and gamma_old.
* Completeness translates gamma by the positive integer (k-R-1)/U and
  sets t=i+f*tau+M2*y. Both positive-coordinate changes are justified,
  not assumed bijections on every unrelated positive assignment.

The degree audit is particularly transparent: Z has degree72 and
nonzero top form 4E0^4 c0^8 T² f0^6; Ninner has top form Z^4 of degree288.
The main residual has degree26 and transport degree2, yielding exact316.
The subtracted term of Ninner has degree at most238 and cannot cancel
that leading form. The statement is uniform for the selected positive
beta and uses no generic-coefficient hypothesis.

This review does not re-prove the inherited native compiler or the
ordinary strong-rank/half-binomial results. Those are explicit imported
mathematical dependencies, not consequences of the finite audit.
