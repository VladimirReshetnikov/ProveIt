# Audit: the finite-field three-term assertion

## Reviewed statement

Radchenko and Zagier, *Arithmetic properties of the Herglotz function*, arXiv:2012.15805v1, Section 7.2, printed page 16, asserts the finite-field identity

`beta_p(n) = beta_p(n+1) + beta_p(n/(n+1))`.

The same assertion was checked in the author-hosted preprint. Here `beta_p(a)` is the rationalized exterior symbol formed from `(1-zeta_p^(a*k)) wedge (1-zeta_p^k)` and finite-field arguments are reduced modulo `p`.

## Exact counterexample

Take `p=7`, `n=2`. Modulo 7, `2/3=3`, while the valid sign and inverse symmetries give `beta_7(3)=-beta_7(2)`. The claimed equation would imply `3 beta_7(2)=0`.

To establish nonzero without assuming the general kernel theorem, write

`a=<1-zeta_7>`, `b=<1-zeta_7^2>`, `c=<1-zeta_7^3>`.

Then

`beta_7(2) = -2 (b-a) wedge (c-a)`.

Let `A=log(2 sin(pi/7))`, `B=log(2 sin(2pi/7))`, `C=log(2 sin(3pi/7))`. At the embeddings indexed by 1 and 2, the two vectors are `(B-A,C-B)` and `(C-A,A-B)`. Their determinant is

`-(B-A)^2 - (C-B)(C-A) < 0`,

because `A<B<C`. This is a strict analytic inequality proving a nonzero image of the exterior symbol. It is not an approximate rank calculation.

## Proposed correction

Remove the universal finite-field three-term statement for this definition of `beta_p`. A different module, action, or quotient would require an explicitly reformulated assertion and proof. Preserve the valid sign and inverse symmetries.

The rational Herglotz boundary formula

`partial xi_(p/q) = beta_q(p) - beta_p(q) - <p> wedge <q>`

is unaffected. It follows directly from finite products. The reviewed ProveIt manuscript already provides this direct derivation and separates it from a finite-field cocycle premise; the article reproduces the direct verification.

## Scope limits

This is a correction to the specific preprint statement inspected. It is not a claim that every version of the journal article or subsequent correction has been audited, or that all cocycle constructions in the paper fail. The valid finite dilogarithm formula, analytic Hecke identity, and their displayed proofs remain the inputs used here. No priority claim is made for noticing this error.
