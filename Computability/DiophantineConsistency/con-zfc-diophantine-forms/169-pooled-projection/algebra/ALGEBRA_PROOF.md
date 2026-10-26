# Exact algebraic reduction from the composed 223-variable equation

## Results and dependency

The input `parent223.json` is the stable factorial-free pooled-power equation
constructed by the companion composition proof. Its canonical SHA-256 is
`ebf82c1646ff38125aaed2bdef0e7fc5c07b67853dda0e781fc459ead0d1e7c4`.
Everything in this folder is an algebraic integer zero-set equivalence; no
additional semantic or consistency assumption enters these transformations.

| Equation | Integer variables | Quadratic residuals | Degree | Collected monomials | Height | Row height |
|---|---:|---:|---:|---:|---:|---:|
| Input | 223 | 160 | 4 | 7801 | 128446 | 256 |
| Balanced218 | 218 | 155 | 4 | 7726 | 45161 | 128 |
| Centered216 | 216 | 153 | 4 | 15158 | 334952 | 384 |

Every declared variable occurs. Each listed equation is literally the sum of
the squares of its supplied quadratic residuals; all collected coefficients
are separately supplied. The correspondence with the input common zero set
is a polynomial bijection over Z. The two final polynomials differ; their
integer zero sets correspond, rather than the polynomials being identical.

## Common-Hessian projection

Let F_0,...,F_(m-1) be quadratic polynomials over Z in n variables. Let d be
an integral vector annihilated by every Hessian. If l_i is the linear part
of F_i, put a_i=l_i dot d. The exact identity

    F_i(x+t*d) = F_i(x)+a_i*t

holds. Suppose d_p=1 and a_r=+1 or -1. For z with z_p=0, set

    t(z)=-a_r*F_r(z),
    G_i(z)=F_i(z)-a_i*a_r*F_r(z), i != r.

All G_i remain quadratic with integral coefficients. The map z -> z+t(z)*d
sends their common zeros to the common zeros of F. Its inverse is
x -> x-x_p*d. To check the inverse, F_r(x)=0 and the shift identity imply
x_p=-a_r*F_r(x-x_p*d). Thus one variable and one residual disappear with
an exact integral restoration. This elementary projection lemma is the
method of repository source159; the application to the combined source is
new here.

The five consecutive instances are below. Indices are zero-based and refer
to the current system at that step, not the original input throughout.

| Step | Dimension before | Pivot p | Omitted row r | Nonzero entries of d | a_r |
|---|---:|---:|---:|---|---:|
|1|223|43|28|d43=1, d44=-1|1|
|2|222|59|45|d59=1, d60=-1, d61=-2|-1|
|3|221|63|48|d61=-1, d63=1|1|
|4|220|30|15|d30=1, d31=-1, d32=-2|1|
|5|219|24|9|d24=1, d26=-1, d27=-2|1|

The frozen certificate gives every restoration polynomial and every
intermediate canonical hash. The checker reconstructs the result by
restriction to x_p=0 and constant row combinations; the discovery program
used multivariate shear and substitution. These are independent exact
implementations of the same identity.

## Balanced endpoint

After the five projections, 38 elementary integer row operations give the
balanced equation. Each operation replaces row i by row i+k*row j, i != j,
and is inverted with -k. Therefore the common zero set is unchanged. The
specific operations are fixed data, not an invocation of an optimizer.

## A centered integral chart for two further projections

In the projected 218-variable system, put

    a=x8, b=x9, u=x19, v=x20, w=x33.

Rows 5 and 18 have the exact affine difference

    -F5+F18 = 4+12*a+16*b+4*u-v+w.

Direct substitution for w makes much larger coefficients. Introduce the
integer coordinates t=u+3*a+4*b+1 and c=v-2*t. This is an invertible affine
change with integer inverse

    u=t-3*a-4*b-1,   v=c+2*t.

All other coordinates, including w, are initially unchanged. The affine
difference becomes 2*t-c+w. Hence set w=c-2*t and omit row5. The retained
row18 becomes c-4*t^2+1. This is a polynomial bijection of integral zero
sets, not a division by 2 or a change in the witness domain.

After deleting w and renumbering, row79 of the 217-variable system is

    x93 +4+3*x8+7*x9-4*x19
        -2*x22-2*x26-2*x28-2*x30-2*x32
        -4*x34-2*x35-2*x38-2*x41-4*x60-2*x61.

Solve it for x93, substitute in every remaining row, and omit it. Its
replacement is affine over Z, so every remaining residual is quadratic.
Finally perform the 59 frozen elementary row operations to obtain Centered216.

## General affine-consequence lemma

Suppose an integral constant combination sum(c_i*F_i) is a positive integer
multiple h*L of an affine integral polynomial L. If L has a coefficient
epsilon=+1 or -1 on x_p, solve L=0 for x_p as an affine integral polynomial.
Substitution preserves degree at most two and gives an integral inverse
restoration. A row r with c_r != 0 may be omitted: at zeros of all retained
rows and L, the identity yields c_r*F_r=0, hence F_r=0 in Z. No unit
assumption on c_r is necessary. This proves the two affine projections.

## Verification and scope

`audit_algebra.py` imports no discovery or construction module. It verifies
all five common-kernel directions, every slope and literal residual,
both inverse affine chart identities, both affine row identities, every
inverse row operation, every collected quartic coefficient, metrics and
coordinate occurrence. Five corrupted certificates are required to fail.
It passes in normal and optimized Python, so correctness checks are not
disabled by `python -O`.

The generic algebraic lemmas establish unbounded equivalences. The finite
certificate audit verifies their hypotheses for these literal polynomials.
The semantic connection to C222 and to ZFC refutation is the explicitly
identified inherited composition theorem. No end-to-end Lean/Rocq replay,
proof of consistency or claim of globally smallest Diophantine equation is
made here. The centered chart is a useful new presentation of this input;
the generic projection and integer row-operation ideas are not new.
