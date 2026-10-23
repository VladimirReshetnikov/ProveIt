# Independent review of the lean eleven-positive theorem

Reviewed: `../positive/Y_ABSORPTION_PROOF.md` and the inert JSON
`../positive/positive11_Y_lean_product.json`.
Candidate SHA256 at review:
`a1cd5cf7ea36f0e323f3ae44c26a78017c4fb8a3b89e88208e549c6790c49fd8`.

## Outcome

No new mathematical gap was found in the ordinary reduction. The proposed
degree954 /113-operation eleven-positive equation is supported by the stated
proof, subject to its explicitly inherited normalized compiler, signed-quotient
Pell interface and K215 calibration. This review is AI-assisted ordinary
mathematical scrutiny, not a new Lean/Rocq certificate or independent human review.

The proof correctly combines three changes that are not immediate substitutions
into the older text: inner-separator removal before recovering h, absorption
modulo Y rather than E, and the lean carrier K=IT, delta=ell.

## Critical proof checks

1. The weaker estimate needed before h is recovered is correct. The identity
   `(Ig)^2-(cf)^2=I^2-c^2` yields `Ig-cf>ic/(8E)>12/E`, using
   `I>=c^2`, `g<2Ec`, and `c>2Y>96`. Separately
   `(b+cf)/d<12/E`. Thus the auxiliary-root error is absorbed without the
   unavailable claim `k>E` or the stronger unnecessary `Ig-cf>1`.

2. The lean carrier excludes the negative main root. Its excess over
   `b+ITg` is `t+u/Y+ell+(b0+g)/H`. The first term is positive because
   `Y>3R`; the last two exceed tau because `(b0+g)/H>c/3>k` and
   `tau<ell+k`. Actual quadratic conjugation is used only after the
   forbidden branch is excluded. No independence of formal sign automorphisms
   is assumed.

3. Exceptional inner denominators are genuinely excluded. `C(x)=0` forces
   `Q|A(A-1)` and `x=0` forces `Q|(A-1)^2`. Both contradict
   `1<A<Delta I=sqrt(Q)`, a bound that remains valid without h. The displayed
   formulas for f' and tau' are therefore justified; rational Pell saturation
   then makes y and x integral.

4. Recovery order avoids circularity: first g,tau',f',y, then only
   `Y|H(k-R-1)`, then the inherited signed-index argument gives p=R and n<R.
   Since `gcd(Y,H)=gcd(Y,3)<=3`, the modulus `Y/gcd(Y,H)>R` is sufficient to
   turn `2n=R+1` modulo that modulus into equality. The recurrence modulo E
   then restores the full `E|k-R-1` and a positive h. Only after this may the
   carrier be divided by Y with `u/Y=hX`, giving the main congruence modulo H
   and positive gamma.

5. Completeness is positive, not merely integral. The proposed carrier has
   `t>=gamma+T(Ig-cf)+(tau-ell)-hX>0`, because
   `tau-ell>k/3` while `hX<k/Y<k/3`. Canonical witness bounds give the
   positive s shift. The optional z shift is justified on canonical zeros,
   not asserted to be a bijection on all positive assignments.

6. The exact-degree argument has the correct matched-factor pattern.
   Four unmatched factors have degree119. For matched f/g signs,
   the residual correction is
   `H(t+ell-sa*tau)+b0-sg*g`, giving degrees107,107,101,97.
   The special factor has nonzero leader proportional to
   `2t-k0-iT*c0/E0`. Their sum is888 before absorption. The prefactor in
   formula(8) is `2^12`, with positive sign: four unmatched factors supply
   `4^4=2^8`, two degree107 factors supply `4^2=2^4`.
   Multiplication by Y^16 adds64 and the transport factor adds2, giving954.

## Independent finite leading-form evidence

`check_positive_leading_form.py` was newly authored for this review. It reads
the candidate only as a JSON DAG and imports no candidate or upstream program.
It evaluates complete univariate polynomials under nine distinct specializations
over primes101,1009,65521, with the actual coherent fixed tuple. It separately
transcribes formula(8), applies the s shift and Y^16 scaling, and checks every
predicted leading coefficient against the full polynomial result.

All nine norm degrees are952 and all nine product degrees954, with nonzero
leading coefficients matching the analytic formula exactly.
`POSITIVE_LEADING_FORM_CHECKS.json` retains the values and candidate hash.
These computations give rigorous degree lower bounds and transcription evidence;
the inspected factor-degree argument supplies the uniform upper bound.

## Correct comparison points

The best prior eleven-positive degree is package38's optional1140/129,
not merely its headline1154/123. Their shifted two-equation points are
1138/124 and1152/118 respectively. The new954/113 product and952/108
shifted system improve both compared presentations. Domains and equation
counts must remain explicit. The historical67-operation scalar equation and
59-operation system optimize another point and remain unbeaten on cost alone.
