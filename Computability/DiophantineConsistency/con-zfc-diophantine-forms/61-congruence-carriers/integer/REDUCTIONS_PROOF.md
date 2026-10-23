# Exact unit eliminations: 37 integer variables in degree six, 34 in degree eight

## The fixed source

Use the literal 45-integer quartic `57-separated-degrees/quartic/quartic45.json`
from the pinned ProveIt snapshot. Its SHA-256 is
`2b4d3d372fd899042eb3db9ee25e085193204640d28009807fde0778bc9528ac`.
Its Git blob SHA-1 is `2fcd266847f5335e35b5853f5125bb9cece7fc0d`,
verified against the repository tree at snapshot
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.
The copied source is `upstream/quartic45.json`; its ordinary mathematical
proof is `upstream/QUARTIC45_PROOF.md`. The **entire** coefficient tuple is
the source's mixed-parity-unrounded-1064921 tuple. The source port `MF`
means the already shifted `MF_source`. No coefficient is changed below.

All variables in this note are unrestricted integers. The source's positivity
conditions are retained algebraically, including after their named
coordinates are substituted out. In particular, no assertion that a positive
coordinate can simply be discarded is used.

## The elementary elimination theorem

Suppose a polynomial system over the integers consists of

    x - A(y) = 0,  F_1(x,y) = ... = F_m(x,y) = 0,

where A has integer coefficients and does not involve x. The maps

    (x,y) -> y,       y -> (A(y),y)

give mutually inverse bijections between its integer solutions and those of
the system F_i(A(y),y)=0. Negating the defining residual does not change this
statement. Iterating this rule gives an integer solution bijection for any
triangular list of such substitutions. No division or root extraction is
involved, and no nonvanishing premise or sign premise is needed.

The proof is substitution in both directions. It is elementary algebra
formalizable in ZFC. Replacing a finite system by the sum of the squared
residuals preserves its integer zeros because every integer square is
nonnegative. Consequently the source's ZFC-provable consistency equivalence
transfers to both constructions below.

## The 37-variable sextic

Write q=beta J+1 and H=4a+3. Write

    p_eta  = 1+eta_pos1^2+eta_pos2^2+eta_pos3(eta_pos3+1),
    p_zeta = 1+zeta_pos1^2+zeta_pos2^2+zeta_pos3(zeta_pos3+1).

In the source remove the eight variables

    Baux, C2, F2, N, w, X, eta, zeta

by their source equations and substitute everywhere as follows:

    Baux = I^2,             C2 = c^2,            F2 = f^2,
    N = q(L+1),             w = u^2,
    X = D-ac-gamma H,       eta = p_eta,         zeta = p_zeta.

Each of the eight displayed equalities is literally one source residual up
to sign. The new system has 37 variables and 20 residuals, each of total
degree at most three. Its sum of squares is the polynomial `sextic37.json`.

The key choice is the reconstruction of X. Substituting w=u^2 into X=wq
would make X cubic. Instead X is supplied by the other source equation,
X=D-ac-gamma H, which is quadratic. The former equation becomes

    D-ac-gamma H = u^2 q.

This is cubic, and substituting the quadratic expression for X into
E=X(a-E) remains cubic. Both w and X disappear within the same degree
budget. The ternary positivity polynomials for eta and zeta are quadratic,
and those two coordinates occur only linearly in the original residuals,
multiplied by at most one other variable.

The residual I-(2r+1)c^2 contains the only occurrence of r in the new
system. Therefore the coefficient of r^2 c^4 in the full sum of squares
is exactly 4. Its exact degree is six on every coefficient slice, including
the authentic source tuple. There are 718 symbolic monomials in the expanded
sum of squares when the four fixed ports are kept as formal symbols.

## The 34-variable octic

Use the same q, H, p_eta and p_zeta. Delete eleven source coordinates by

    L = q^2-1,              N = q^3,             X = wq,
    D = wq+ac+gamma H,      Delta = a^2+H,
    C2 = c^2,              F2 = f^2,            Baux = I^2,
    g = y^2-V^2,           eta = p_eta,         zeta = p_zeta.

The order in `build_reductions.py` is triangular, and the equation for N is
the retained source definition after L has been eliminated. The remaining
34 variables and 17 residuals are listed literally in `octic34.json`.
Each residual has degree at most four.

For instance, the surviving auxiliary equation is

    y^2-I^2(y^2-V^2)-1 = 0,

and the surviving strong equation is

    I^2-(a^2+4a+3)(f^2-1) = 0.

The latter has coefficient -1 on a^2 f^2, while every other residual has
degree less than four in the pair a,f. Thus the coefficient of a^4 f^4 in
the sum of squares is exactly 1. The final degree is exactly eight,
independently of the fixed coefficient ports. The symbolic expanded sum of
squares has 814 monomials.

## Semantic statement and boundary

For either listed polynomial P, the local reductions prove an exact
integer-solution bijection with the fixed Q45 source. Consequently, using
the source's ordinary Pell/native-compiler/calibration theorem,

    ZFC proves [there is no integer tuple with P=0] iff Con(ZFC).

This is a mathematical reduction and exact finite algebra certificate. It
is not a newly compiled end-to-end proof-assistant formalization, a proof of
consistency, or a global optimality result. The new equations improve
variable counts at their indicated degrees; they do not beat the existing
ten-integer-variable constructions at high degree.

## Reproduction

Run `python3 build_reductions.py` from this directory (or use an absolute
path). Only the standard library is needed. The program reads the literal
source as data; checks that each deleted residual is exactly plus or minus
the proposed unit definition; performs all substitutions over exact sparse
integer polynomials with symbolic ports; expands the sum of squares; checks
all variable/port liveness, counts, degrees and the stated leading
coefficients; and emits both JSON packets and `REDUCTION_VERIFICATION.json`.

The checks do not use removable Python assertions and can also run with
`python3 -O`. The exploratory `search.py` and `search*.json` files are not
dependencies of either construction or its proof. `eliminate.py` provides
the exact sparse arithmetic; its optional search mode is not a minimum
certificate and can be omitted from a minimal release after retaining the
arithmetic routines used by the builder.
