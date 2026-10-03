# Local Boolean degree and a fully expanded quartic certificate

Supplement to the independently reviewed core construction in `PROOF.md`.
This supplement concerns one local transition only. It makes no statement
about unbounded reachability, a uniform simulation of arbitrary rules, or
Diophantine finite-fold results for arbitrary recursively enumerable sets.

## 1. Sixteen signed exact-component indicators

For a primitive input A and anchor a, put `H=A+a+[-2,2]²` and define

`M_A,a(c)=∏_{p∈A+a}c_p · ∏_{q∈H\(A+a)}(1−c_q)`.

On binary inputs this is one exactly when A+a is an isolated component. If
B is its corresponding primitive output, the local Boolean function at z is

`g(c)_z=c_z+Σ_rules Σ_{b∈B\A} M_A,z−b(c)−Σ_rules Σ_{a∈A\B} M_A,z−a(c)`.

This equality is justified on all binary configurations by the unique-
recognition and disjoint-output proof, not just along the intended orbit.
There are respectively 2, 4, 4, and 6 translated indicators of types E, W, R,
and L. Each input halo is a rectangle of height five and widths respectively
6, 7, 8, and 9. Hence the indicator degrees are 30, 35, 40, and 45.

On finite supports, summing this local expression over z also proves
conservation directly: the translate sum of each indicator is the same at
every offset, while `|B\A|=|A\B|` for each rule. Only finitely many indicators
can be nonzero, so all rearrangements of these sums are legitimate.

## 2. Exact Boolean degree and essential dependency rectangle

The displayed polynomial is multilinear in its input bits, since no indicator
uses any bit twice. Its six L-indicators have distinct translated rectangular
halos of size 45. Their degree-45 coefficients are the respective signs,
because each L indicator has 42 zero-factors and `(-1)^42=1`. The six distinct
top monomials cannot cancel one another, and all remaining indicators have
degree at most 40. Thus the unique real multilinear polynomial representing
the local Boolean function has degree exactly 45.

The six L halos have x-intervals `[-2,6],[-5,3],[-6,2]` and y-interval
`[-3,1]` for the three birth terms, and x-intervals
`[-2,6],[-4,4],[-6,2]` with y-interval `[-2,2]` for the three removal terms.
Their union is exactly `[-6,6]×[-3,2]`, a set of 78 cells. Every such variable
therefore occurs in at least one nonzero degree-45 monomial.

A variable appearing in the unique multilinear polynomial of a Boolean
function is essential. Indeed, if the function did not depend on that bit,
the polynomial obtained by subtracting its zero and one restrictions would
vanish on the entire Boolean cube; uniqueness of multilinear interpolation
would force that derivative polynomial to be zero identically. This would
remove every monomial containing the bit, a contradiction.

Consequently G has precisely this 78-cell dependency set and exact centered
Chebyshev radius six. The shifted rule F has the translated dependency set
`[-6,6]×[-4,1]` and exact radius six as well. These are properties of the two
specified rules; they make no claim of least possible radius among all
binary mass-four examples or any larger class.

There is also a direct check independent of the degree argument:
`audit/essential-input-witnesses.json` gives, for each of the 78 cells, two
finite inputs differing at that cell only and having different central
outputs. `audit/check_essential_inputs.py` verifies these with both the direct
and local evaluators for G and F, using explicit exceptions under normal and
optimized Python. The quartic checker independently finds witnesses as well.

## 3. A quartic with exactly one auxiliary tuple

Throughout this supplement, natural integers include zero: `N={0,1,2,...}`.

Let the 78 input bits in row-major order on `[-6,6]×[-3,2]` and one output y
be external variables, for 79 externals in total. Evaluate each of the sixteen
indicators in its own unshared multiplication chain, with all occupied factors
first and all complementary factors afterward. Start each chain with its
first external occupied factor. For every remaining multiplication introduce
one new natural auxiliary z and impose one of

`z−uv=0` or `z−u(1−v)=0`,

where u is the preceding value and v is an external input bit. Thus there are

`2·29+4·34+4·39+6·44=614`

auxiliaries and 614 multiplication residuals. Add all 78 bit residuals
`c_i(c_i−1)` and one output residual

`y−c_0−Σ_birth last_product+Σ_removal last_product`.

The resulting polynomial P is the sum of squares of these 693 residuals.
Each gate residual has degree at most two, so P has degree at most four.
The bit constraints supply uncancelled fourth powers of external variables,
so its degree is exactly four.

For each binary external input, the acyclic multiplication chains force all
614 auxiliaries uniquely, one after another. Their values are all zero or
one, so they are natural witnesses. The output residual forces y to equal
the local CA output. Conversely, when y is correct, these forced values make
every residual zero. Because P is a sum of real squares, P=0 holds exactly
when all residuals vanish. Consequently, for each fixed external input/output
tuple, the natural auxiliary fiber has size one if it is a valid binary local
transition and size zero otherwise.

The same uniqueness holds over unrestricted real auxiliary variables: each
input-bit residual first forces its external input into `{0,1}`, and each
chain equality still forces its next value uniquely. No claim is made that
614 is an optimal auxiliary count; this is the deliberately unshared count.

## 4. Exact resource ledger and literal expanded polynomial

The initial occupied-factor gates give

`2·1+4·1+4·2+6·2=26`

plain-product residuals, each having two monomials. The complementary-factor
gates give

`2·28+4·33+4·37+6·42=588`

residuals, each with three monomials. The 78 input-bit residuals each have two
monomials. The output residual has 18 monomials. Thus:

| Resource | Exact count |
|---|---:|
| External input bits | 78 |
| External variables including output | 79 |
| Natural auxiliaries | 614 |
| Total variables | 693 |
| Squared residuals | 693 |
| Residual-monomial occurrences | `26·2+588·3+78·2+18=1990` |
| Ordered SOS-expansion occurrences | `26·4+588·9+78·4+18²=6032` |
| Distinct collected expanded monomials | 3403 |
| Largest absolute collected coefficient | 2 |
| Total degree | 4 |

`local-quartic-certificate.json` contains the literal collected expanded
polynomial with all 3403 terms, the complete variable order, all 693 residuals,
all 614 gate instructions, and the sixteen indicators. A monomial lists its
variable indices with repetition, and its value is the product of those
variables. Coefficients and exponents are exact integers; no floating-point
algebra is involved.

`code/build_local_quartic.py` builds the artifact. The separate
`code/check_local_quartic.py` does not import the builder. It reads the actual
exported artifact and independently re-expands the SOS using unordered pairs,
compares the exact sparse polynomial, evaluates valid local witnesses against
the cylinder evaluator, rejects wrong outputs and every single-auxiliary
perturbation, checks the polynomial identity at nonbinary integer points, and
finds direct essentiality witnesses for all 78 cells. Every check uses an
explicit exception and remains active under Python -O. These computations
supplement the unique-witness argument above; finite sampling does not prove
that argument by itself.
