# Two derived signs in the frozen mixed667 family

All unknowns in this packet range over **the unrestricted integers**.
Let `P` denote the frozen667-coordinate,585-row system, let `Q994` denote
the frozen mixed994 system, and let `Q988` denote `guarded.json` here.
The equation represented by a row list is the sum of the squares of all
its listed residuals, equal to zero. This packet proves

    exists x in Z^988, Q988(x)=0
      iff exists y in Z^994, Q994(y)=0
      iff exists z in N^667, P(z)=0.

The second equivalence is the frozen mixed994 ordinary theorem, including
its signed-index recovery and explicit positive-comparison reconstruction.
The first equivalence below is a literal bridge to that theorem. It
introduces no new arithmetic calibration assumption. The original source
and its fixed coefficients remain unchanged. No Lean or internal-model
formalization is claimed for this new packet.

## 1. The exact equation and coordinate identities

Keep all585 rows of `source/natural667.json` verbatim. Of the109 guard
indices in `source/route_sign.json`, remove precisely294 and461. For each
remaining index v, in its original order, append the row

    x_v - a_v^2 - b_v^2 - c_v(c_v+1).

Use three fresh private integer coordinates per row. Thus there are
667+3*107=988 unknowns and585+107=692 quadratic residuals. This gives the
literal quartic `Q988`. `domain_certificate.json` records every guard and
`BRIDGE994.json` records every old/new witness slot.

Equality of the **entire variable metadata records**, not equality of
names, identifies the following raw and contracted coordinates:

| Value | Raw1259 coordinate | Contracted667 coordinate |
|---|---:|---:|
| t0 | 0 | 0 |
| A | 644 | 294 |
| T | 694 | 326 |
| D | 917 | 461 |

The t0 and T guards, at contracted indices0 and326, are retained. The
raw coordinates t=4 and n=5 are omitted affine wires, with the exact
restoring polynomials `t=1+x_0` and `n=2+x_0`.

All592 raw affine restoring polynomials are copied unchanged from the
frozen mixed994 packet. They are triangular monic definitions over Z.
The independent checker substitutes them into **every one** of the1177
original raw rows. Exactly585 become the retained rows, coefficient for
coefficient and in order; the other592 become zero. This assertion needs
no sign or natural-number interpretation of a restored wire.

## 2. Four actual original-row identities

Write r_i for zero-based raw row i. With n=raw5, A=raw644, T=raw694 and
D=raw917, the checked identities are

    r0 = t-t0-1,
    r1 = n-t-1,
    r644+r643+r642-r640-n*r639+r641 = 2*A*n-T-n^2-1,
    -r853-r852+r598 = D-A^2+1.

They are full polynomial identities in the1259 raw coordinates. In
particular, the multiplier of r639 is the polynomial -n, not the
constant -1. They are valid before any Pell or power semantics is used.

At a `Q988` zero the guards give t0,T>=0. Integer restoration and the
first two rows give t>=1 and n>=2. The third identity gives

    2*A*n=T+n^2+1.

If A<=1, its left side is at most2n, whereas its right side exceeds2n:
`T+(n-1)^2>=1`. Thus A>=2. The last identity gives D=A^2-1>=3. In
particular, both omitted guard values are nonnegative.

The supplied four certificates conservatively certify the lower bounds
t>=1,n>=2,A>=2,D>=2. The checker verifies them by writing each identity
as x*F-G=0, proving F>0 and G-(L-1)F>0 after shifting only earlier known
lower bounds. An integer x<=L-1 would contradict that identity. For the
A certificate, after n=z+2 the shifted factor is2z+4 and the shifted
gap is `T+z^2+2z+1`. For D, after A=a+2, the shifted gap for L=2 is
`a^2+4a+2`. These have nonnegative coefficients and a positive constant;
their odd-degree operands have already been proved nonnegative. Only
the two retained t0/T guards are used as initial signs in this argument.

## 3. The literal988-to994 bridge

For an integer x, the row

    x=a^2+b^2+c(c+1)

has integer witnesses iff x>=0. Soundness follows from squares and the
fact that consecutive integers have nonnegative product. For completeness,
4x+1 is positive, odd, and congruent to1 or5 modulo8, hence is not of
the excluded form4^r(8s+7). Legendre's three-square theorem represents
it as three squares. Modulo4 exactly one summand is odd. After permuting
the summands, write the two even roots as2a,2b and the odd root as2c+1;
division of the resulting identity by4 gives the displayed row.

Given a `Q988` zero, leave all667 body values unchanged. Copy all107
guard triples into their exact old994 positions. The previous section
proves A,D>=0, so choose three integer witnesses for each of those two
values. Put the A triple into slots865,866,867 and the D triple into
934,935,936. These six fresh witnesses fill the entire remaining target
auxiliary set. All585 body rows and every one of the109 old guard rows
now vanish. This is an **actual literal `Q994` zero**.

Conversely, from any integer `Q994` zero, keep all667 body values and
copy its107 surviving triples into their new slots. Discard exactly the
two A/D triples. Every `Q988` row then vanishes. These two constructions
prove the first existence equivalence without any claim that an
arbitrary `Q988` tuple is pointwise natural.

The frozen994 theorem can now be applied. Its nonpointwise step recovers
the requested power meanings using the signed-index theorem and replaces
private comparison data by fresh natural data at

    B' = B+4*V*U*(A+1).

All its detailed hypotheses, complete private-use ledger and coefficient
bindings are inherited from its sealed packet. This new bridge does not
replace that theorem by a bounded computation or reuse a natural Pell
criterion on signed comparison coordinates.

## 4. Fresh integer monic projections

Each child packet has a complete signed monic elimination certificate.
For a deleted coordinate x_v, its defining row gives a polynomial
`x_v=R` with integer coefficients and no x_v on the right. The defining
row is removed, and this exact polynomial is substituted into every
remaining row, **including all107 guard rows**. The forward map is
coordinate restriction. In reverse order the stored recipes restore all
deleted coordinates uniquely over Z; every deleted row becomes zero and
every surviving row becomes its parent row. No unconstrained coordinate
is discarded. Intermediate recipes need no positivity property.

Always reverse every such integer elimination first, obtaining a literal
988-coordinate zero. Only then apply the four raw-row bounds and the
994 bridge. This order prevents a signed restoration from being mistaken
for a natural-number preservation theorem.

The independent verifier checks every substitution/inverse, then a
separate sparse collector expands the entire sum of squares. Every
coordinate is live and the exact degree is4. The complete integer
polynomial coefficients are stored in each `expanded_polynomial.json`.

| Variant | Integer unknowns | Rows | Collected terms | Maximum absolute coefficient |
|---|---:|---:|---:|---:|
| unprojected | 988 | 692 | 5149 | 63905862 |
| support4 | 729 | 433 | 5989 | 63905891 |
| support8 | 703 | 407 | 9006 | 2445790974704 |
| support16 | 701 | 405 | 9101 | 2445790974704 |
| support32 | 700 | 404 | 10437 | 2445790974704 |

Compared with the corresponding frozen994/735/709/707/706 endpoints,
each saves exactly6 unknowns,2 residuals and28 collected terms, at the
same coefficient height. These are complete quartics, not local gadget
counts. The frozen source, source calibration, earlier candidates,
current equation page and their files are unmodified.

## 5. Verification boundary

`build.py` imports the authenticated generic signed optimizer only as a
producer. `check.py` never imports that optimizer. It uses its separately
authenticated verifier and repository polynomial/bound routines. It
checks complete frozen inputs, all1177 raw row identities, all107 guard
equations, every literal994 witness slot, the four strict bounds, every
signed inverse, every collected coefficient, exact quartic degree and
liveness. It also reruns the complete frozen994 checker in the current
Python optimization mode. Negative controls reject changed raw recipes,
row multipliers, bound order/strength, missing prerequisite guards,
coordinate identities, target witness slots, inverses, coefficients and
rows. Small all-sign guard diagnostics supplement the universal argument
above; they do not prove it.

The new work is an ordinary mathematical existence equivalence plus
finite exact polynomial verification. It neither restarts the paused
Lean work nor claims a new internal-ZFC consistency theorem.
