# Shared remainder bounds reduce the ordinary direct quartic

## Result and scope

The delivered file `pair69/support8/polynomial.json` is an explicit polynomial
with fixed, literal integer coefficients in **592 unrestricted integer
unknowns**. Its degree is exactly four. It has **8,167 nonzero monomials**,
and its largest absolute coefficient is **2,445,790,974,704**. The equivalent
sum of squares in `pair69/support8/equation.json` has 372 quadratic residuals.
Every coefficient is present, rather than given by a checksum or an
uninstantiated coefficient parameter.

At the immutable repository commit
`84e16e43092614bae262ca59651cb9d77e31a255`, the corresponding ordinary
75-predicate direct construction has a matched 604-variable, 9,676-monomial
quartic of the same height. This packet regenerates that matched baseline
from its actual source body. The new result saves twelve actual unknowns and
1,509 monomials at the same degree and coefficient height. It is not the
fewest-variable equation among all branches: the native/Pell branch has
far fewer unknowns and much larger fixed coefficients. The benefit is a
smaller complete literal-coefficient quartic on the independent C222 route.

The sole new unbounded argument is the elementary sign recovery below. It
precedes every interpretation of a power, factorial, Pell index or source
computation. The existing ordinary C222/refutation calibration is inherited
through the unchanged 75-predicate parent. This packet does not newly prove
that calibration, run Lean, or provide an encoded internal-ZFC derivation.
Conditional on the accepted parent theorem, the new equivalence is an
ordinary proof formalizable in ZFC, with no consistency assumption.

## 1. The reusable lemma

Let integers r,s,a,b,B satisfy

    r+s+1=B,  a+b+1=B,  a>=0,  b>=0.

Then

    (r>=0 and s>=0)  if and only if  r*s>=0.

The forward implication is immediate. For the reverse implication,
r+s=a+b>=0. If r<0, then r*s>=0 implies s<=0, whence r+s<0, a
contradiction. The same argument excludes s<0. No division by a witness,
strict positivity of r or s, size bound, or intended interpretation of B
is used. The boundary B=1 is covered: both r and s must be zero.

Thus several interval remainder tests can share the evidence that their
common upper bound is nonnegative. Once one remainder/slack pair is kept,
each additional pair needs one quadratic product condition rather than two
independent scalar conditions.

The representation used for a nonnegative integer is

    n=a^2+b^2+c(c+1),  a,b,c in Z.

Every represented value is nonnegative because c(c+1)>=0 for integral c.
Conversely, 4n+1 is not of the excluded form 4^u(8v+7), so Legendre's
three-square theorem represents it as three squares. Reduction modulo four
shows that exactly one of the three coordinates is odd. Relabeling gives
4n+1=(2a)^2+(2b)^2+(2c+1)^2, proving the representation. Accordingly the
condition r*s>=0 is represented by the single quadratic row

    r*s-a^2-b^2-c^2-c=0.

The two old scalar guards require six private unrestricted coordinates;
the new product guard uses three. Actual projected counts must still be
measured, since the product may keep a source coordinate alive.

## 2. Six applications in the complete existing body

The following are indices of the *original raw body*, not the final
592-coordinate equation. `PAIR_GUARD_CERTIFICATE.json` records both the raw
and compact source rows whose exact sums establish the displayed identities.
Rows are zero based. The shared anchors are retained unchanged.

| New product pair (r,s) | Common B | Retained anchor (a,b) | Raw rows for B-r-s-1 | Raw rows for B-a-b-1 |
|---|---|---|---|---|
| (585,586) | 574 | (576,577) | 553,554,555 | 547,548,549 |
| (593,594) | 574 | (576,577) | 559,560,561 | 547,548,549 |
| (601,602) | 574 | (576,577) | 565,566,567 | 547,548,549 |
| (619,620) | 608 | (610,611) | 578,579,580 | 572,573,574 |
| (637,638) | 626 | (628,629) | 591,592,593 | 585,586,587 |
| (562,563) | 547 | (549,550) | 537,538,539 | 526,527,528 |

For example, the unchanged rows 553--555 are

    -raw585-raw586+raw589=0,
    -1-raw589+raw590=0,
    raw574-raw590=0.

Their sum is raw574-raw585-raw586-1=0. Rows 547--549 similarly prove
raw574-raw576-raw577-1=0. The two anchor values raw576 and raw577 still
have their original scalar guards, so they are nonnegative before any
source semantics is invoked. The new product guard therefore recovers
both removed scalar signs. Each other row in the table has the same
complete coefficient certificate, independently checked.

The transformation keeps 63 of the 75 original predicates, removes the
twelve listed scalar predicates, and adds the six products. The resulting
domain has 69 predicates. In particular it preserves the strict common-V
predicate, the earlier paired-index predicate, and the factorial lower
bound. It neither weakens the early factorial sign bootstrap nor assumes
the twelve removed signs in order to recover them.

## 3. Exact existence equivalence before projection

Let x denote all 1,259 original integer body coordinates. Let B(x)=0 denote
its 1,177 quadratic rows. Write the old predicates as G_j(x)>=0. The old
polynomial is the sum of the body-row squares and the squares of

    G_j(x)-a_j^2-b_j^2-c_j^2-c_j.

The new polynomial has exactly the same body, the 63 retained guards, and
the six product guards above. All its residuals are quadratic.

Given a zero of the new polynomial, every residual is zero because it is
a sum of integer squares. Every retained or product predicate is therefore
nonnegative. The six exact row identities and their unchanged anchors
recover all twelve omitted scalar predicates by the lemma. Choosing fresh
three-square witnesses for those twelve nonnegative values produces an
old 75-predicate zero at precisely the same body tuple x. This restoration
is complete before applying any previous ordinary source theorem.

Conversely, an old zero has all twelve scalar values nonnegative. Their
six products are therefore nonnegative. Keep the same body tuple and all
63 retained guard triples; choose fresh triples for the six products.
This gives a new zero. In fact the two systems have exactly the same
projections onto their body-coordinate space. Their private guard witnesses
need not be unique or correspond bijectively.

All steps are elementary integer arithmetic apart from the standard
three-square representation. They formalize in ZFC. Composing with the
existing 75-predicate ordinary source theorem yields

    ZFC |- [no integer zero of the new polynomial] <-> Con(ZFC).

This is an equivalence and does not assert either side. The original
C222 source/refutation calibration remains the named dependency, rather
than being replaced by finite computation.

## 4. Complete literal quartic and degree-preserving projection

The unprojected new system has

    1259+3*69 = 1466 variables,
    1177+69 = 1246 quadratic residuals.

The included projection deletes a coordinate only from an actual monic
row v-f=0 or f-v=0, with integral f. It substitutes f in every remaining
row and verifies that every result still has degree at most two. Each
step has a unique integer inverse, so it is a bijection of the full
integer zero sets. No nonnegative-coefficient condition is needed for
these unrestricted integer coordinates. No unconstrained variable is
dropped: every deleted coordinate has an explicit restoration.

For the principal profile there are 874 such eliminations, leaving 592
coordinates and 372 quadratic rows. The matched old profile makes 880
eliminations, leaving 604 coordinates and the same 372 rows. Six fewer
quadratic eliminations are possible after introducing the product guards;
this is why the actual saving is twelve variables instead of the naive
eighteen-variable guard-count saving.

The final equation is

    P_592(z_0,...,z_591) = sum_{j=0}^{371} E_j(z)^2 = 0,
    z_0,...,z_591 in Z,

where `pair69/support8/equation.json` supplies every literal E_j. The
fully collected polynomial in `polynomial.json` supplies every coefficient
of P_592 independently of that notation. The checker expands all squares
by its own integer polynomial arithmetic and compares the entire sparse
polynomial coefficient by coefficient. Its maximum monomial degree is
four with nonzero terms of degree four, establishing exact degree.

Three additional raw/compact settings and two raw support caps retain
independent projection certificates. The main tradeoffs are:

| Profile | Integer variables | Residuals | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| Matched original75, raw support8 | 604 | 372 | 4 | 9676 | 2445790974704 |
| New69, raw support8 | 592 | 372 | 4 | 8167 | 2445790974704 |
| New69, quadratic-first support32 | 598 | 378 | 4 | 7617 | 6956012 |
| New69, raw support16/affine2 | 603 | 383 | 4 | 7086 | 964213 |
| New69, compact support32 | 592 | 372 | 4 | 8465 | 2445790974704 |

Raw support16 and support32 have the same metrics as the principal
support8 result; their exact construction histories remain supplied.
These settings are a measured finite comparison, not an exhaustive search
or a global optimality proof.

## 5. Reproduction and assurance

Run from this directory:

    python3 -B build_pair_guards.py
    python3 -B extra_profiles.py
    python3 -B check_pair_guards.py

The producer uses the preserved upstream optimizer. The checker imports
neither producer nor optimizer. Its separate projection checker verifies
every actual row deletion, retained variable map, and integral inverse.
The new checker independently verifies all old/new predicate rows, the
complete source-row identities, the anchors' availability, all copied
Git blob identities, and all coefficients of each expanded quartic.
Deliberately changed source-row and output-coefficient controls are rejected.
The checks are exact finite algebra. The sign proof and the two-way
witness construction above carry the unbounded arithmetic argument.

`SOURCE_PROVENANCE.json` binds the 16 copied upstream text files to their
exact Git blob identifiers and SHA256 values at the immutable commit.
The original 75-predicate parent, its prior ordinary sign proof, and its
source dependency ledger are included. The inherited calibration chain
is not recursively replayed by this new checker. Its boundary is explicit.

The construction does not depend on the K215 machine table or on Jones's
universal expression. It retains the independent direct C222 arithmetic
source used by its parent. No claim of priority outside the inspected
repository is made for the interval-sign lemma.
