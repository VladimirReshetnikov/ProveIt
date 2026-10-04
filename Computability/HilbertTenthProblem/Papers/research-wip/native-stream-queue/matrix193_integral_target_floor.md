# Three target gates under the inherited integral group projection

The bare Pell391 target has first row

    (chi + 52500 psi, -29036 psi),

which costs **3=2M+1A** from independently supplied chi,psi. One can conjugate
the repeated matrix to obtain the tempting target `(chi,84 psi)`, costing
one multiplication. However, that change destroys first-row injectivity
on the inherited twenty-letter group H'. In fact **every integral
unimodular basis change that permits a generic first-row target circuit
with at most two gates destroys that same group-wide injectivity**.

This is a scoped obstruction to improving this target interface by a
global GL2(Z) basis change while retaining its existing group projection
proof. It is not a universal Diophantine lower bound. Nor does a collision
somewhere in H' alone prove a false accepted semigroup input: a different
argument exploiting a smaller set of actual products remains possible.
The exact Pell index and unbounded positive-product certificate remain
unpaid. Rational bases, other projections, additional supplied ports,
relations imposed only at Pell points, and changed alphabets are outside
the lower-bound model.

## 1. Reduce to a simple integral frame

Use the complete [Gamma1(5) recoding](matrix193_gamma1_recode.md), with

    T=[[1,1],[0,1]], U=[[1,0],[5,1]],
    V=[[-9,5],[-20,11]], H'=V^-1 H V.

The group H contains T and U: in the original tape basis they are the
conjugates of `ab` and `b^-1`. Its repeated block before conjugation is

    W0=T^3 U^-2=[[-29,3],[-10,1]].

Conjugating by U gives

    W1=U^-1 W0 U=[[-14,3],[65,-14]],
    D=W1+14I=[[0,3],[65,0]], D^2=195I.

Since U belongs to H, this conjugation leaves H itself unchanged. Thus
the integral frame `V^-1 U` carries the actual group H' to H and the
actual repeated block to W1. Arbitrary integral unimodular changes of
the original frame correspond exactly to arbitrary such changes here.

The even block is

    B1=W1^2=391I-28D=[[391,-84],[-1820,391]].

Its inverse powers have first row `(chi_391(x),84 psi_391(x))`. But H
contains U, and I and U have the same first row. Therefore this explicit
one-gate form loses the property used to replace full matrix equality
by first-row equality. The failure concerns every group element, the
scope of the inherited projection theorem, rather than the scalar Pell
identity itself.

## 2. Classify all equal-diagonal integral frames

Suppose S is integral with determinant epsilon=±1 and

    S^-1 D S=[[0,b],[c,0]].

Here bc=195. Changing the sign of the second basis vector changes the
signs of both b,c, so initially assume c>0. Write the first column of S
as `(p,r)`. Its second column is forced by `D(p,r)=c*second_column`.
Taking determinants gives the necessary equality

    Q(p,r)=65p^2-3r^2=c*epsilon,
    c in {1,3,5,13,15,39,65,195}.                    (1)

The following complete modular certificates leave only Q=-3 and Q=65.
Each entry is a modulus at which the indicated value is absent from the
image of Q; the saved receipt lists every residue in each finite image.

| c | Exclude Q=-c modulo | Exclude Q=+c modulo |
|---:|---:|---:|
| 1 | 5 | 5 |
| 3 | survives | 9 |
| 5 | 13 | 13 |
| 13 | 8 | 3 |
| 15 | 13 | 13 |
| 39 | 5 | 5 |
| 65 | 3 | survives |
| 195 | 25 | 25 |

These are unrestricted congruence obstructions, not a search bounding p
or r. They can also be checked immediately from the square residues at
the displayed small moduli.

If Q=-3, reduction modulo 3 gives p=3h, and (1) becomes

    r^2-195h^2=1,
    S=[[3h,r],[r,65h]]=C J,
    C=[[r,3h],[65h,r]], J=[[0,1],[1,0]].              (2)

If Q=65, reduction modulo 5 and 13 gives r=65h, and

    p^2-195h^2=1,
    S=[[p,3h],[65h,p]]=C.                            (3)

Thus these are sufficient as well as necessary descriptions. The omitted
negative c case adds a right factor E=diag(1,-1).

All matrices C in (2)-(3) are signed powers of W1. To see this without
assuming a classification of quadratic ideal classes, a norm-one unit
`r+h sqrt(195)>1` with integer coefficients has h>=1 and r>=14.
Its smallest possible value is consequently `14+sqrt(195)`, and that
value is indeed a unit. Multiplication by its inverse reduces any larger
positive unit to the interval [1,14+sqrt(195)); the only unit in that
interval is 1 by the same integer-coefficient bound. Signs and inverses
cover all remaining units. In matrix form,

    14I+D=-W1^-1.

Therefore C lies in ±H. Every possible equal-diagonal frame consequently
conjugates H to one of

    H, E^-1 H E, J^-1 H J, (JE)^-1 H (JE).

The first two contain a nonidentity lower unipotent from U. The last two
contain one from T, because J interchanges the upper and lower directions.
All four groups therefore fail first-row injectivity. This classifies
all integral equal-diagonal frames, including arbitrarily large bases.

## 3. Two generic gates cannot avoid this obstruction

For an arbitrary integral frame write

    S^-1 D S=[[u,v],[w,-u]], u^2+vw=195.

In particular v is nonzero: otherwise the integer u would square to 195.
The first row of the inverse even-block power is

    (chi+28u psi, 28v psi).                           (4)

The cost model has only independent supplied chi,psi and arbitrary fixed
integer constants. Each binary addition, subtraction or multiplication
costs one gate; wire reuse is free. Both outputs must agree with (4) as
polynomials in the two independent supplied coordinates. No index or
norm equation is used to simplify the computation.

If u=0, the first output is a wire and the second needs one multiplication.
Section 2 has already excluded every such frame with inherited group-wide
injectivity. Suppose u is nonzero. Both outputs now need gates, since
28u and 28v are nonzero integers of magnitude at least 28. A single gate
from the initial ports cannot produce the first output: addition or
subtraction would give psi coefficient ±1, and multiplication cannot
produce its two linear terms. Hence in any circuit with at most two gates,
the first gate must produce the second output `28v psi`; the other gate
then combines that output with chi. The only possibilities matching the
chi coefficient 1 are addition and subtraction, which require u=±v.
This argument also excludes a nonlinear first gate: with two needed
outputs it must itself equal the linear second output.

When u=±v, conjugation by the integral lower shear

    L=[[1,0],[-u/v,1]]

makes both diagonal entries zero, preserving the off-diagonal entry v.
Conjugation by a lower shear preserves whether first rows are injective:
the new first row is the old first row multiplied on the right by L,
because the first row of L^-1 is (1,0). Right multiplication by L is
invertible. An injective first-row frame with u=±v would therefore give
an injective equal-diagonal frame, contradicting Section 2.

The current H' frame has its already proved group-wide first-row
injectivity and admits the three displayed target gates. Thus **three
is optimal in this precise model**. It is not claimed optimal after
restricting the observable product set, adding other paid registers,
changing the witness interface, or changing the underlying encoding.

## 4. Exact evidence

The [fresh helper](matrix193_integral_target_floor.py) and
[receipt](matrix193_integral_target_floor.json) authenticate the full
Gamma1 author trio as inert bytes/data. They verify the actual tape-letter
identities, the change to W1, and all fourteen modular exclusions covering
the complete divisor/sign list. These finite residue certificates prove
their unrestricted exclusions because every integer has a residue at
each stated modulus. The remaining Pell classification is the elementary
descent argument above, not a finite enumeration.

Seventeen signed-index Pell fixtures check both surviving matrix families
and 68 explicit lower-unipotent collisions. Sixteen symbolic-integer shear
instances cover the divisor/sign alternatives. Twenty-one exact indexed
powers corroborate the original three-gate bare target. The proof explains
why the Pell descent, shear identity and gate argument apply without
these finite bounds. No predecessor script or archived executable runs.

Run from any working directory:

    python3 matrix193_integral_target_floor.py --root /absolute/path/native-stream-queue --expect /absolute/path/matrix193_integral_target_floor.json

The writer uses `--output FILE` instead. Explicit exception checks remain
active under optimized Python; input JSON rejects duplicate and nonfinite
values, and receipt comparison distinguishes exact JSON types. No new
universal Diophantine operation bound follows.
