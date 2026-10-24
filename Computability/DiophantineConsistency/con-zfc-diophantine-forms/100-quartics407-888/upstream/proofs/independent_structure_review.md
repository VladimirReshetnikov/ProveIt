# Targeted audit of the fully synchronized direct compiler

Audited files: `notes/synchronized_builder.py`, `notes/shared_power.py`,
`notes/shared_product_power.py`, `notes/direct_source_factored.py`, and the
literal files under `notes/frozen_source/`. Exact source hashes are in
`FROZEN_SOURCE_CHECK.json` and its optimized counterpart. This is an ordinary
mathematical and exact finite audit, not a newly checked ZFC proof term.

## Mathematical assessment

The earlier global-frame, deferred-binomial, eleven-coordinate and exponent-majorant arguments in `GLOBAL_POWER_AND_MAJORANT_AUDIT.md` continue to apply. Two further transformations are sound.

### One auxiliary Pell point and CRT base

Given the finitely many canonical indices at common A, let `Y_i=psi_A(k_i)>0`.
In the finite ring `(Z/LZ)[s]/(s^2-(A^2-1))`, with `L=4 product_i Y_i^2`, the
class `A+s` is a unit: `(A+s)(A-s)=1`. Some positive power is1. Its ordinary
Pell coordinates U,V satisfy `U=1 modL`, `V=0 modL`, with V>0. Hence each
Y_i^2 divides V, U is odd, and the Pell norm implies gcd(U,V)=1. Thus U is coprime to M=4V.

The final code imposes one product condition `V=(product_i Y_i^2)(v+1)`
instead of the separate divisibility rows. The chosen V satisfies this
stronger condition. CRT now gives a common B with `B=A modU` and `B=1 mod4V`. Take a positive
representative B>A. For all i simultaneously choose
`S_i=chi_B(k_i)`, `R_i=psi_B(k_i)`. Polynomial congruences give
`S_i=X_i modU`, `R_i=k_i mod4Y_i`, and monotonicity supplies the nonnegative
quotients used by the literal code. As B>1 and B=1 mod4V, write B=1+4V(q+1) with q natural. Since every
Y_i divides V, all old divisibility quotients `(B-1)/(4Y_i)-1` are
nonnegative. The one product and one B condition therefore restore every
old index certificate. This proves simultaneous completeness, not just
individual solvability of each old gadget. Soundness follows immediately
because the shared rows supply every old index certificate.

The finite ring, product modulus and its period occur only in this proof;
none is a hidden coordinate in the final polynomial.

### Factoring the common axiom side condition

Write `s=p^2+q^2`, let d_0=v and let d_1,...,d_8 be the eight unconditional
axiom differences. Let `g=(v-bundle)^2+guard^2`. The old axiom disjunction
is the zero set of

`product_(j=0)^8 (s+d_j^2) * (s+g)`.

All factors are nonnegative. Its zero set is exactly

`s=0 and (some d_j=0 or g=0)`.

The new polynomial

`s + (product_(j=0)^8 d_j)^2 * g`

has exactly the same zero set, again by nonnegativity. The modus-ponens and
generalization factors are unchanged and nonnegative, as are the later
accumulator/beta residual squares. Their complete local acceptance zero set
is therefore preserved. The common constructors and the suffix outside this
branch block are AST-identical to the already audited eleven-coordinate
source. This is a zero-set equivalence, not an equality of the old and new
polynomials; the new majorant must be recomputed, and it is.

## Exact implementation checks

`verify_synchronized.py --product-index --factored-source --equation-dir notes/frozen_source`
passes both normal Python and Python `-O`. It checks:

- The inherited source changes by precisely the two deleted beta remainder rows; the factored source retains the exact constructor prefix and accumulator/beta suffix.
- All388 exponent-majorant inequalities and D=6,893,159. The emitted exponent N=8,388,608=2^23 is the least power of2 above D, so H=R^N remains a valid majorant and requires only23 squarings; its exact literal power expression is checked.
- One common power frame,27 power requests,22 exponent certificates,10 base moduli, and one common auxiliary index triple. The literal global V product contains exactly all22 squared ordinates and one positive quotient; the actual B expression is exactly1+4V(q+1).
- Syntactic positivity of all27 power exponents and all14 binomial upper/lower arguments.
- The common binomial exponent is exactly the sum of every distinct upper input, with none omitted or repeated; the common radix is its certified power of2 plus1.
- Exact equality of the selected class/source regeneration with the delivered residuals, variable ordering and expanded polynomial.
- Independent sparse expansion/collection of every squared residual, exact degree, coefficient height and variable liveness.

The audited intermediate has:

| Quantity | Exact value |
|---|---:|
| Nonnegative integer coordinates | 895 |
| Quadratic residuals | 773 |
| Expanded quartic monomials | 4,863 |
| Maximum absolute coefficient | 63,908,265 |
| Total degree | 4 |

The previous1151- and969-coordinate stages are separately recorded in
`SYNCHRONIZED_CHECK.json` and `FULLY_SHARED_CHECK.json`; their counts are
not the frozen source count.
Any subsequent terminal/affine contraction has a separate certificate and
must not be conflated with this source audit.

Supplementary fixtures check52 common-radix digit extractions,504 oriented
Pell quotient identities, and five explicit common-unit-ring/CRT families
for A=2,...,6 and indices1,2,3. These finite fixtures do not replace the
universal proofs above. The inherited C222, Horn-flow, CRT, factorial and
Pell–Matiyasevich calibrations remain explicitly named ordinary theorem
dependencies.
