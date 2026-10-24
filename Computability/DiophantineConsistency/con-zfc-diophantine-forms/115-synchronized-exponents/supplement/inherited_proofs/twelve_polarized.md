# Free J and polarized auxiliary norm

This is a complete literal equation with **12 strictly positive integer
unknowns**, **96 live binary operations** and exact degree **70**, with the
unchanged whole compact44 coefficient tuple. It is the same polynomial
as the incoming 98-operation free-J parent. All source definitions and
the four fixed coefficient payloads are retained under `source/positive/`.
MF is the already shifted source mask, used exactly once.

The previous ordinary 12-positive point cost100 operations. Promoting its
restricted `J=6j+1` to a free positive input saves two operations by the
new ordinary congruence proof. The exact tail identity below saves two
more. No claim of smallest possible equation is made. This incremental
result does not replace the established canonical printed page under the
user's current presentation policy.

The witness list is

```
J,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma > 0.
```

`equation.json` contains all96 binary operations, the full input/port
inventory and output. The fixed ports are beta,K0,MC,MF. All twelve
unknowns, all ports and every operation are live; squaring and scalar
multiplication each cost one. The census is53 multiplications,
26 additions and17 subtractions.

The arithmetic improvement is local. With arbitrary integers d,Q,V,n put

```
p=1-Q,  w=n+V,  Cy=QV^2-1,  h=p*w^2+Cy.
```

Then

```
(d*h+Q*p)^2-d*Q*(2*p*w)^2
    = (d*h-Q*p)^2+4*d*Q*p*Cy.
```

Indeed subtracting the right side from the left gives
`4*d*Q*p*(h-p*w^2-Cy)=0`. This is a polynomial identity over every
commutative ring. In the complete equation d=c^4. The literal parent
tail computes the left side in17 operations; the new shared-Cy tail
computes the right side in15. Both also compute the same h.

The prefix before this block and the entire unit-product suffix are
unchanged. Induction through the arithmetic circuit therefore proves
pointwise equality of the complete old and new polynomials for every
integer input and every integer port value. In particular their positive
zero sets agree exactly. The free-J parent supplies the ordinary source
and refutation equivalence; its complete unbounded proof is retained in
`source/positive/PROOF.md` and independently reviewed in
`../../reviews/congruence-certificates-peer.md`.

Polynomial identity transfers the parent's reviewed degree upper bound70
and its nonzero selected leading coefficient64*beta^18. The independent
checker also finds degree70 on full-circuit diagonal slices at the actual
fixed tuple modulo1009,1013 and1019. No new bound, auxiliary witness,
quotient, sign assumption or calibration premise is introduced.

`CUT_IDENTITY.json` retains both literal blocks and the precise boundary.
`check.py` imports no builder: it symbolically collects the universal
four-variable tail polynomial, checks unchanged surrounding gates,
topology/liveness/counts, the complete coefficient binding, actual-tuple
degree slices and signed whole-circuit controls, and rejects an altered
norm tail. The generic norm has32 collected terms. All source files are
copied exactly from the original archive, SHA256
`f4119b01e56f586558f0910c6deb21b83c82dfc324f884d7d95d28500ef09e63`.

From the repository root, with SymPy available:

```sh
python -B Computability/DiophantineConsistency/tools/build_free_j_polarized_positive.py --check
python -B Computability/DiophantineConsistency/candidates/free-j-polarized-positive/check.py
python -B -O Computability/DiophantineConsistency/tools/build_free_j_polarized_positive.py --check
python -B -O Computability/DiophantineConsistency/candidates/free-j-polarized-positive/check.py
```

This is ordinary mathematical research and reproducible literal data.
Lean remains paused. The inherited internal object-ZFC derivation is a
separate outstanding requirement; this identity proves neither consistency
nor absence of zeros.
