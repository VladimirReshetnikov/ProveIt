# Review of the actual-modulus source scout

**PASS after one boundary-scope correction.** The single displayed rewrite
is a complete86=48M+38A source for exactly the current84 polynomial. It
provides no saving and no circuit lower bound. The norm-product
nondivisibility statement is valid on every inherited compiler slice.

Reviewed author pins:

- PY: `e40ebeb0d14c6a9ababe977107f12afbe234f0297d40f3d6f488c6eae781e9af`
- JSON: `962aff0fc5e070d03d6ab55c29819163fb69360e291d2e5d26efc0c07cfd06c8`
- MD: `068c5efb6d2fc6d011334d4e0cf7384e5d6d048ec64cee1c2161bb126cb173a1`

Root read the entire helper and proof. The new main root expands
`a*(c+4sigma)+X+3sigma+rho*H`; the actual two paid H rows give H=4a+3,
so this is exactly `a*c+X+(rho+sigma)*H`. The input-root construction is
unchanged. Reading the emitted row replacement confirms the independent
coefficient identity is applied to the actual producers. Downstream
expression interning checks all seven factors and the final output; the
topological/liveness check retains all86 rows and25 supplied ports.
The parent exact degree187 therefore transfers as a full polynomial
identity. The fixed products4sigma and3sigma are paid, accounting for the
loss of1M+1A against84.

For the uniform rational specialization, q=2 follows from Jrep=1/Bm1.
Then X=1, Y=a0/2 and a=Y*(X+1)=a0. Setting eta=zeta=0 makes c=0.
Taking x=-b/ell and delta=0 makes kappa=0; F=Z=0 and alpha=b+1 give
W=2-(b+1)+b=1. The two zero quotient witnesses make both roots1, so
Nm=Ni=1. At a0=-3/4, H=0; at a0=-1, Delta=0. These evaluations
disprove divisibility of Nm*Ni by H or Delta over the actual supplied
ports, for any nonzero fixed Bm1 and ell, hence for every valid slice.

The first draft incorrectly said these were not complete polynomial zeros.
The Delta=0 specialization is necessarily a complete signed rational zero
of F84, because F84=Delta*F85. The final note now states this explicitly
and excludes only positive integer zeros and compiler counterexamples.
This correction does not alter the source, receipt or nondivisibility
argument. The argument concerns Nm*Ni only and does not contradict the
known discriminant factor of the complete output.

Fresh installed-path normal and optimized exact replays pass. The32
rational source assignments and two boundary evaluations supplement the
formal identities. No predecessor code, earlier census or historical
compiler was executed. Larger joint schedules and positive zero-set
coordinate changes remain open.
