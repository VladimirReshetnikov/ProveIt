# Residue-affine steps: a paid polynomial and an affine-input obstruction

This packet gives a complete positive-witness **one-step** polynomial for
one-register residue-affine maps and an ancestor-pumping theorem for their
unit-slope subclass with a pure-division branch. Even point-target acceptance
and an arbitrary fixed positive affine input loader cannot make that subclass
represent every recursively enumerable set: every infinite accepted language
contains an affine geometric progression, so it cannot be exactly the factorials.

This extends the archived
[two-branch odd-loader result](legacy-untracked/current/1980/EXPLORATION_TWO_BRANCH_COLLATZ_PRIMITIVE.md)
to arbitrary radix, a full table of residue branches, and arbitrary positive
affine loaders. It is distinct from the
[residue-EXIT obstruction](../../1980/EXPLORATION_TRANSLATED_COLLATZ_INPUT.md):
the acceptance test here is reaching one fixed integer. The established
complete universal bound remains **75=41M+34A**.

## 1. Model and source boundary

Fix b>=2 and integer tables a_r,d_r, for 0<=r<b. On positive integers put

    f(n)=a_r floor(n/b)+d_r,        r=n mod b.               (1)

Assume these formulas map positive integers to positive integers. The
polynomial step construction below works for arbitrary such fixed tables.
For the pumping theorem impose the additional hypotheses

    a_r>0, gcd(a_r,b)=1 for all r,
    a_0=1, d_0=0, and d_r>=1 for r>0.                     (2)

Thus f(bn)=n, and all branch slopes are units modulo b. Equivalently

    f(n)=(a_r n+c_r)/b,    c_r=bd_r-a_r r.                (3)

Translations c_r can be negative; the positive-domain hypotheses are
nevertheless satisfied by (2).

Generalized Collatz maps form a serious computational substrate, but the
precise subclass and input convention matter. The broader global
undecidability result is
[Kurtz and Simon, 2007](https://doi.org/10.1007/978-3-540-72504-6_49);
its all-input eventual-reaching question does not establish the fixed-map
ordinary-input contract needed here. A recent primary treatment,
[Carelli, ICALP 2026, Section 4](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.175/LIPIcs.ICALP.2026.175.html),
uses the same coprime-slope generalized-Collatz convention and relates
unresolved dynamics to one-variable loop termination. Neither source is
being cited for universality of subclass (2). The theorem below is a direct
deduction with a fully stated boundary, not a decision procedure for its
individual trajectories.

## 2. Complete positive one-step relation

Introduce only two positive existential coordinates q,s. Their meanings are

    q=floor(n/b)+1, s=(n mod b)+1.

Interpolate fixed rational polynomials of degree at most b-1 through the
table values a_r and d_r-a_r at s=r+1. Clear all denominators by one fixed
positive numeral L, obtaining integer polynomials P,G with

    P(r+1)=L a_r, G(r+1)=L(d_r-a_r).

Then y=f(n) is equivalent to the three equations

    n+(b+1)=bq+s,
    Ly=P(s)q+G(s),
    J(s)=product_(i=1)^b(s-i)=0.                          (4)

Indeed the last equation forces s in {1,...,b}; the first gives the unique
Euclidean quotient and residue with q>=1. The second is exactly (1).
Conversely the actual quotient and residue provide positive witnesses,
including n<b. No external selector mask or residue oracle is used here.

The following is a generic literal DAG, without coefficient-specific
simplifications. Fixed numerals and equalities are free; every numeral
multiplication is paid.

| Source part | M | A |
|---|---:|---:|
| First equation | 1 | 2 |
| Two padded degree-(b-1) Horner evaluations | 2b-2 | 2b-2 |
| Selector product J | b-1 | b |
| Second equation after Horner evaluation | 2 | 1 |
| Total | 3b | 3b+1 |

Thus the three-equation one-step graph costs **6b+1**. Degree-lowering,
constant-one and shared-coefficient optimizations can reduce a particular
table; this is not an optimality claim. Signed intermediate registers and
signed polynomial coefficients are permitted; the supplied coordinates
n,y,q,s remain positive.

If a literal single polynomial is wanted, compute the two first-equation
residuals R1,R2 and use

    R1^2+R2^2+J(s)^2=0.

This adds two subtractions, three squarings and two additions, giving
**6b+8=(3b+3)M+(3b+5)A**. This is a complete scalar polynomial with two
positive witnesses. A generic fixed affine input n=ell*x+e costs another
1M+1A. None of these local counts supplies a finite-iteration certificate.

## 3. Pumping one sufficiently long accepted itinerary

Fix a positive target tau and loader n=ell*x+e, with ell>=1 and ell+e>0,
so every positive x loads a positive integer. Accept iff a finite iterate
of n equals tau; time zero is allowed. The map, target and loader are fixed.

Factor ell=ell_parallel*ell_perp, where ell_parallel contains precisely
the prime-power factors of ell whose primes divide b, and gcd(ell_perp,b)=1.
Let nu be the least nonnegative integer for which

    ell_parallel divides b^nu*tau.                      (5)

This finite threshold is effectively computable by ordinary factorization;
it is used in the proof, not supplied as a free arithmetic primitive.

Suppose input x0 has an accepted itinerary n0,...,n_t=tau of length t>=nu.
Composing its branches gives fixed integers A>0 and C with

    b^t*n_t=A*n0+C, gcd(A,b)=1.                         (6)

Here A is the product of the branch a_r values. Let lambda>=1 satisfy

    b^lambda=1 modulo A*ell_perp,

using lambda=1 when that modulus is one, and put R=b^lambda>1. Such a
lambda exists by coprimality. For every k>=0 define

    n_k=(b^t*R^k*tau-C)/A,
    x_k=(n_k-e)/ell.                                    (7)

These are integral positive inputs, x_0 is the original input, x_k is
strictly increasing, and every x_k is accepted.

To prove integrality and loader alignment, subtract the original value:

    n_k-n0=b^t*tau*(R^k-1)/A.                           (8)

The quotient is an integer and a multiple of ell_perp, because R^k-1
is divisible by A*ell_perp. It is also a multiple of ell_parallel by
(5), since A is coprime to ell_parallel. The two factors of ell are
coprime, proving n_k=n0 modulo ell. All differences are nonnegative and
strictly increase with k, so x_k>=x0>=1.

Moreover (8) is divisible by b^t. The lifted trajectory follows the same
first t residue branches: after j steps its difference from the original
trajectory is positive or zero and divisible by b^(t-j). For j<t this
forces the same next residue, and division by b preserves the induction.
The positivity of each a_r keeps every lifted state positive. At time t,
equation (6) gives the lifted state R^k*tau=b^(k*lambda)*tau. Exactly
k*lambda uses of the pure-division branch then reach tau.

The original prefix and these explicit division steps are a full accepting
run; no untested assumption about later Collatz behavior is involved.

## 4. The raw-input language cannot be arbitrarily thin

For each fixed duration t there are finitely many accepted starting values:
each of the at most b^t branch itineraries has at most one preimage of tau,
since its composed slope A/b^t is positive. Therefore an infinite accepted
language has an accepted itinerary with t>=nu. Formula (7) yields

    x_k=alpha*R^k+beta, alpha>0, R=b^lambda>1,             (9)

with rational alpha,beta and integral x_k. In particular successive ratios
x_(k+1)/x_k tend to the finite value R. The affine recurrence
x_(k+1)=R*x_k+T has a fixed integer T, since its first two terms are integers.

The factorial language {j!:j>=1} contains no such infinite increasing
sequence: successive distinct factorials j!<l! have ratio at least j+1,
which tends to infinity. Consequently **no table satisfying (2), no point
target and no fixed positive affine loader represents exactly factorials**.
This excludes universal representation of recursively enumerable sets,
even allowing the table, target and affine loader to depend on the set.

There is also an explicit restriction on finite accepted languages. The
first t branches depend only on n modulo b^t. The loader's residue class
meets at most b^t/gcd(ell,b^t) such classes. A finite accepted language
therefore has at most

    sum_(0<=t<nu) b^t/gcd(ell,b^t)                       (10)

members. An accepted input with any longer itinerary would pump to an
infinite family. If nu=0, every nonempty accepted language is infinite.
If b is a prime power, b^t divides ell for every t<nu, so (10) reduces
to at most nu members. The old binary loader 2x+1 with odd target has
nu=1, recovering its one-member finite exception. For example a_1=3,
d_1=3 and target5 accepts only x=2 under that loader: every other odd
start immediately enters multiples of3, which remain multiples of3.

## 5. Escape routes and unpaid history costs

The theorem does not cover a numerator slope sharing a prime with b,
removal of the pure-division residue, guards using more residue digits
than the single denominator step, nonlinear input substitutions, extra
rejection/interval guards, or non-point acceptance. It does not prove
decidability of the accepted languages within its scope. In particular it
does not decide the ordinary Collatz conjecture or any untested trajectory.

Those exclusions identify actual resources that a proposed universal map
must use before this inexpensive scalar circuit is worth integrating.
The one-step graph (4) itself also works with nonunit slopes, so a future
construction escaping the pumping theorem could retain that primitive.
An iteration compiler still must certify the chosen residue at every time,
coefficientwise products with history digits, bounded carries, common
finite geometry, the ordinary input and its accepting endpoint. Applying
P to a packed selector integer evaluates a polynomial of that integer;
it does not perform independent table lookup at every digit. Hence the
6b+1/6b+8 counts cannot be multiplied or inserted into complete75 as a
history-saving claim.

## 6. Exact evidence

The [checker](residue_affine_ancestor_pumping.py) compiles the interpolation
constants with rational arithmetic and audits both scalar DAGs. It tests
independently supplied wrong quotients, selectors and outputs, rather than
only witnesses obtained from the update. For pumping it takes finite
known trajectories, constructs the new ordinary inputs, independently
simulates their entire prefixes and division tails, and checks the affine
geometric recurrence. Radices2,3,4,6 exercise both prime and composite cases;
loaders include factors shared with the radix and coprime factors. The
itinerary/residue bijection is separately exhausted through length4.
Directly solving the inverse branches also checks12,000 finite-depth
loader bounds independently of the forward itinerary enumeration.

The [receipt](residue_affine_ancestor_pumping.json) records the exact finite
counts; the proof above establishes the unbounded theorem. Run:

```sh
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_ancestor_pumping.py
```

Independent proof/source review and default replay passed without findings.
That review also tested160 varied unit-slope tables at radices2,3,4,5,6,8,10,12,
covering141 geometric progressions,423 complete lifted histories, and2,400
finite-depth bounds. It checked the composite-radix loader factorization,
depth threshold, prime-power simplification, factorial obstruction, positive
quotient/residue witnesses, both operation schedules, and the scoped primary
source statements. These additional experiments corroborate the proof and
do not classify any untested trajectory.
