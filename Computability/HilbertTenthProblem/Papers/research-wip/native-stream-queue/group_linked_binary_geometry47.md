# A repunit population kernel links duration and matrix height

A **47=26M+21A** component, with **13 equations** and **19 strictly
positive auxiliary coordinates**, links the matrix height parameter q
to the cell duration. It reuses a supplied register `B=8q^2`, as computed
by [canonical history47](group_four_register_canonical_history47.md).
Its standalone version computes that register in two additional products
and costs **49=28M+21A**.

The component's exact positive projection, under `B=8q^2`, is

    J>B,       J odd,       q=2^popcount(J).             (1)

Combining it with the separately certified conditions

    P is a power of two,       (B-1)J+1=P               (2)

gives exactly

    q=2^t,       B=8q^2,       P=B^t,       t>=2.        (3)

Conversely every geometry(3), with J its cell repunit, has a strictly
positive extension to this component. Thus the two exponents in(3)
are linked; no comparison of uncharged logarithms is being imposed.

The prescribed-scale [selected-source119](native_binary_masked_selection63.md)
can supply the dyadic condition in(2). The
[regular controller](group_regular_macro_controller.md) already pays
the repunit equation. Neither relation is included in47 or49 here.
The complete source composition, its ordinary-input contract and a joint
ledger must be checked separately before claiming a universal bound.

## 1. The exact source and its positive domain

Take the unchanged binary43 core used by
[binary three-selector53](native_binary_three_row_fifo58.md), but supply
no selector fields and no packing equations. Alias its input index r
to the shared repunit coordinate J, and its scale `n2` to q. The core's
sixteen remaining positive coordinates are

    a,c,d,f,h,i,j,k,o,s,w,tau,eta,zeta,ga,y_aux.

Write r=J in the proof and abbreviate

    X=wq, Y=sq, E=XY, A=a+2, Delta=A^2-1,
    ell=2r+1, U=jc-ell.

The ten core comparisons are

    (E^2+X)(kY)^2=tau(tau+1),
    c=kY+eta, k=eta+zeta, k=r+1+hE,
    a=Y(X+1), d=X+ac+ga(4a+3),
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    (ic^2)^2*(U^2-y_aux^2)=1-y_aux^2,
    U=of-c.                                            (4)

Supply three further positive coordinates `odd_half,bound_beta,index_beta`
and compare

    s=2*odd_half+1,
    r+bound_beta=X,
    B+index_beta=r.                                    (5)

They cost1M+3A beyond the core's25M+18A. All thirteen comparisons
are retained; no residual has been treated as a free side condition.
The source uses only binary addition/subtraction and multiplication,
charging every square and every multiplication by a fixed numeral.

The shared source has positive parameters q,B,J and nineteen positive
auxiliaries. Its theorem explicitly assumes the containing source has
computed B=8q^2. The standalone source has parameters q,J and adds
`q_squared=q*q; B=8*q_squared`, making that identity internal. In both
versions computed U may have either sign away from the zero set.

The [checker](group_linked_binary_geometry47.py) exposes
`build(shared_B=True)` and `build(shared_B=False)`, each returning its
literal source, comparison list, parameters, auxiliaries and counts.

## 2. Bootstrap without a selector-packing bound

Take a positive zero of(4)--(5), with B=8q^2. Before any power or
population conclusion, positivity gives

    r>8q^2>=8, r>=9, r>q,
    X>r, Y>=3q>=3,
    E>r+1, a=Y(X+1)>2r+1.                             (6)

Put `P0=2XY^2+1`. Then P0>A>1; for example
`P0-A=XY(2Y-1)-Y-1>0` follows from X>=10,Y>=3.
The first norm in(4) is equivalently

    (2tau+1)^2-(P0^2-1)k^2=1.

The usual Pell classification gives `k=psi_P0(n)` for n>=1. Modulo E,
P0=1 and the Pell recurrence gives `k=n mod E`. The positive index
equation implies `n=r+1 mod E`; since `0<r+1<E`, n>=r+1>=10.
The main norm gives `c=psi_A(p),d=chi_A(p)` for p>=1. Since P0>A and
`c>Yk>k`, strict monotonicity in the parameter shows

    p>=n+1>=r+2>=11.                                  (7)

The needed strong-rank and signed-index bounds still hold at this
smaller bootstrap:

    c>(2A-1)^(p-1)>A^10>A*Delta^2,
    c>2p,
    c>Yk>6n>=6(r+1)>2ell.                             (8)

For the last line, `psi_P0(n)>2n` for n>=10 and P0>1, and Y>=3.
These statements use no bound such as `r<q^3`, no supplied digit fields,
and no assumption q>=2. In particular the preliminary case q=1 has
not been silently discarded.

The retained [strong auxiliary rank theorem](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
applies to the actual square `(ic^2)^2`, using(8). It gives an auxiliary
index m with

    f=chi_A(m), c divides m, m>=c>2p,
    ic^2=Delta*psi_A(m).

Now U=jc-ell>0 by(8), and Pell growth gives f>2c. The retained
[half-parameter signed-index argument](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)
uses exactly these bounds and the unchanged two minus congruences.
It yields `p=ell=2r+1`: the possible congruences `ell=+p or -p mod c`
reduce to equality because both ell and p lie in `(0,c/2)`.
The [fixed-minus parity theorem](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
then gives r odd. Its generic sign argument likewise uses c>2p,
m>=c>2p and f>2c, not a selector packing or a canonical auxiliary index.

Also n=r+1 exactly. If the residue representative were larger, then
`n>=r+1+E>2r+1=p`; monotonicity would force `k=psi_P0(n)>psi_A(p)=c`,
contrary to c>Yk. Hence

    k=psi_P0(r+1), c=psi_A(2r+1), d=chi_A(2r+1).      (9)

## 3. Ratio estimates at r>=9 and exact population

Here the estimates can be checked directly, without importing a large
packing threshold. For any integer T>1 and n>=3, the Pell recurrence
gives

    (2T-1)^(n-1)<psi_T(n)<(2T)^(n-1).

Apply these inequalities to(9), and put

    xi=(X+1)^(2r)/X^r,       V=XY^2.

Since `a=Y(X+1)`, they give

    c/k > xi*(1+3/(2a))^(2r)*(1+1/(2V))^(-r) > xi,
    c/k < xi*(1+2/a)^(2r).                            (10)

The second strict inequality in the first line follows from `6V>a`,
which holds already at X>=10,Y>=3. The supplied interval c/k<Y+1 and
the lower bound xi>X^r give, by integrality,

    Y>=X^r,       a>X^(r+1).                          (11)

Thus `4r/a<1/2` for r>=9. The elementary estimate
`(1+z)^n<1/(1-nz)<=1+2nz`, for 0<nz<1/2, turns(10) into

    c/k<xi*(1+8r/a),
    0<c/k-xi<16r/(X+1),                              (12)

where xi<Y+1<2Y was used in the second line. This ordering is important:
the small-error estimate is used only after the lower ratio has proved
the much stronger(11).

The sequence `chi_A(j)-a*psi_A(j)` starts with1,2 and obeys the main
recurrence. Modulo `4a+3`, the sequence2^j obeys the same recurrence,
because `4-4A+1=-(4a+3)`. The exponent equation in(4) therefore implies

    X=2^(2r+1) mod (4a+3).

Both representatives lie between0 and a. Indeed X<a, and by(11)

    2^(2r+1)=2*4^r < (r+1)^(r+1) <= X^(r+1) < a.

Consequently

    X=2^(2r+1).                                      (13)

In(12) the error is now below1/2 for every r>=9. The fractional part
of xi satisfies

    0 < sum_(j=1)^r binom(2r,r-j) X^(-j)
      < 4^r/(2X)=1/4.

The latter bound uses that the sum of the lower-half binomial
coefficients is strictly less than4^r/2. The positive ratio interval
`Y<c/k<Y+1`, together with(10)--(12), now forces

    Y=floor(xi)
     =binom(2r,r)+sum_(j=1)^r binom(2r,r+j)X^j.        (14)

Since q divides X, write q=2^u initially with u>=0. The paid bound
r>q ensures `u<2r+1`, so 2q divides X. Reduction of(14) modulo2q and
the oddness of s=Y/q yield

    v2(binom(2r,r))=u.

The factorial valuation identity gives
`v2(binom(2r,r))=popcount(r)`. Thus q=2^popcount(r), automatically
excluding q=1. Together with r odd and the paid index bound, this is
the soundness direction of(1).

## 4. Every positive converse coordinate

Conversely assume(1), with r=J and B=8q^2. Thus r>=9 is odd and
q=2^popcount(r). Define X by(13), Y by(14), and

    w=X/q, s=Y/q, odd_half=(s-1)/2,
    bound_beta=X-r, index_beta=r-B.

They are positive integers: the central-binomial valuation proves s
odd, while Y>=X^r and r>q imply s>1. The other positive differences
follow from X=2^(2r+1)>r and r>B.

Construct the remaining initial kernel coordinates afresh:

    a=Y(X+1), A=a+2, Delta=A^2-1, E=XY, P0=2XY^2+1,
    k=psi_P0(r+1), tau=(chi_P0(r+1)-1)/2,
    c=psi_A(2r+1), d=chi_A(2r+1),
    eta=c-kY, zeta=k-eta,
    h=(k-r-1)/E, ga=(d-X-ac)/(4a+3).                   (15)

The ratio bounds(10)--(12), now evaluated at these constructed values,
and the fractional-tail bound prove `Y<c/k<Y+1`, so eta,zeta>0.
The first congruence makes h integral and strict Pell growth makes it
positive. P0 is odd, so tau is a positive integer. The direct exponent
congruence makes ga integral. Also
`d-ac=2c-psi_A(2r)>c>X`, making ga positive.

For completeness, all remaining strong auxiliary coordinates can be
given by the same generic positive construction as the binary53 proof.
Set ell=2r+1 and

    m=2c*ell, f=chi_A(m), T=Delta*psi_A(m), i=T/c^2,
    y_aux=psi_T(ell), U=chi_T(ell)/T,
    j=(U+ell)/c, o=(U+c)/f.                           (16)

The multiple-index identity gives `c^2 | psi_A(2c*ell)`, so i is a
positive integer. Odd ell makes U integral. As r is odd, ell=3 mod4;
the normalized odd-index congruences give `U=-ell mod c` and
`U=-c mod f`. Hence j,o are positive integers. The Pell identities
give both strong auxiliary norms and both minus congruences in(4).
All sixteen retained coordinates and all three new slacks are therefore
strictly positive. This proves the full converse at every admitted r,
not merely at a bounded set of canonical examples.

## 5. Linking the physical duration

Now add the separately paid relations(2). From(1), q is dyadic, so
B=8q^2=2^d for some d>=1. Write P=2^ell. The repunit equation and
positive J imply `2^d-1` divides `2^ell-1`, hence d divides ell by
division with remainder of the exponents. Therefore, for some t>=1,

    P=B^t,       J=1+B+...+B^(t-1).

The index bound J>B excludes t=1, so t>=2. Since B is a power of two,
these t summands occupy distinct binary positions, giving popcount(J)=t.
Equation(1) now yields q=2^t, proving precisely(3).

Conversely, for any t>=2 take(3) and its displayed repunit J. Then J
is odd, J>B, and popcount(J)=t. The positive converse in Section4
supplies all nineteen auxiliaries. All arithmetic that establishes
B=8q^2, P's dyadic type and the repunit equation remains in its actual
containing components; these shared identities have not become free
operations because they appear in this composition proof.

## 6. Evidence and scope

The [source and receipt](group_linked_binary_geometry47.json) retain the
actual binary43 DAG with only the two input aliases. Both47 and49
variants are audited against thirteen independently expanded residuals
on512 arbitrary positive supplied tuples apiece. The core's saved hash
also records the exact imported instruction sequence.

The checker tests the bootstrap inequalities including preliminary q=1,
and twelve exact Pell ratio prototypes at odd r=9,...,31. These verify
the claimed rounding, valuations and positive partial-kernel coordinates;
they are explicitly not claimed to satisfy the new repunit index bound.
The positive full auxiliary extension is the parametric proof above.
Linked geometries of every duration2,...,128 and an independent search
over dyadic P divisibility candidates check the final population argument.

Default execution compares the entire saved receipt; `--write` refreshes
it. The checker imports the existing binary53 source, so its Python
environment needs that module's SymPy dependency. No numeric search is
used as a substitute for the unbounded ratio, rank, parity or converse
arguments. A complete matrix/controller/selection composition is a
separate source audit and is not claimed by the47-operation subtotal.

An independent root proof/source/default review passed after correcting
the strict upper elementary Pell estimate to n>=3 (equality holds at
n=2). Every use here has n>=10, so the correction changes neither
the theorem nor its source. The reviewer independently derived the
ratio estimates, lower-ratio bootstrap, exponent representatives,
rounding and population recovery, and checked the positive converse.
A second independent full proof/source/default review also passed with
no findings. Its separate binary-powering implementation in the quadratic
integer ring checked17 odd indices r=9,...,41, verifying the ratio,
valuations, and positive h and ga partial-kernel coordinates. The review
also checked the preliminary q=1 case, the strong-rank hypotheses without
packing bounds, and every restored positive auxiliary. The trio is frozen
at the displayed source.
