# Independent mathematical review: thirteen-integer five-root construction

This reviews the mathematical interface and the subsequently checked literal graphs. It is an internal AI-assisted review, not external peer review or a proof-assistant certificate. Literal graph hashes and exact audit results are recorded in `COMPACT_INDEPENDENT_AUDIT.json`.

## 1. Residue calculation before any equation is assumed

Use J=6j+1, q=beta*J+1, W=4(3w+1), X=qW, Y=(2v+1)q^3, a=Y(X+1), H=4a+3, Delta=(a+2)^2-1. The fixed beta is odd and greater than 17. Thus q is even and nonzero; |q|>=beta-1. The nonzero multiple-of-four W gives X divisible by eight, and Y is divisible by eight. Therefore a is divisible by eight, H is odd, and Delta=3 modulo 8. Moreover the same magnitude bound as for the sixteen-variable proposal gives Delta>1 on every integer assignment, without using any source residual.

Let c=2c0+1 and i=2r+1. Both are odd and nonzero. Put

    I=Delta*i*c^2,
    F2=1+Delta*i^2*c^4,
    Q=I^2,
    delta=Q-1.

Then F2=4 modulo 8 and 1+Delta*c^2=4 modulo 8. Since |I|>=Delta>1, delta>0 unconditionally. The quotient Fhalf=F2/4 is an odd integer. The actual literal graph uses `16H^2*F2=64H^2*Fhalf` directly, so no division occurs in its polynomial.

One division-free definition is: write a2=a/2 using the already even radix q; let d=a2(a2+2), u=r*c^2+2c0(c0+1). Then

    Delta=4d+3,
    i*c^2=2u+1,
    Fhalf=d+1+Delta*u(u+1),
    4Fhalf=F2.

These are exact polynomial identities. Because a is divisible by eight, d is even, so Fhalf is odd even before any norm equation is imposed.

## 2. Five-root separation

Write A=1+XY^2(XY^2+1)k^2; this is 1 modulo 4. Let Bguard=4bguard+1 be the existing joint positivity residual with its private p3 coordinate removed. Define the five radicands

    d0=H^2*A,
    d1=1+Delta*c^2,
    d2=16H^2*Bguard,
    d3=64H^2*Fhalf,
    d4=256H^2*delta*(Q*V^2-1).

The first four have exact 2-adic valuations 0,2,4,6. The last has valuation at least 8 whenever nonzero. Its sign is unrestricted before the equation. If it vanished it would already be an integer square.

The five-root norm is the product over all 32 signs of

    x-e0*sqrt(d0)-e1*sqrt(d1)-e2*sqrt(d2)-e3*sqrt(d3)-e4*sqrt(d4).

This product is an integer polynomial, because changing any radical sign permutes its factors. A zero gives a rational signed sum of the five radicals. Grouping terms by square classes over Q and using linear independence of distinct square classes, every irrational class would have to cancel. Within a class, the integer coefficients of the first four terms have distinct 2-adic valuations 0,1,2,3, and the final coefficient has valuation at least 4 whenever it shares one of these classes. Hence no nonempty class sum can vanish. All five radicands are integer squares. This argument covers negative radicands without assuming their positivity: a nontrivial negative class cannot survive a rational sum.

## 3. Recovering the omitted main congruence

Put b0=X+ac, which is even, and supply the carrier

    x=H(2t+1)+b0.

After choosing signed square roots witnessing the zero, all their contributions except the d1 root are divisible by H. For example, if an integer z has z^2=H^2*A, then z/H is a rational square root of the integer A and hence an integer. The same argument handles the factors 4H and 8H in d2 and d3, and 16H in d4.

Consequently the signed main root D obeys D=b0 modulo H. Since H is odd and never zero, gamma=(D-b0)/H is an integer and restores the parent's exact main Pell row. In particular no external divisibility witness is required. Because d1=4 modulo 8, D is even; b0 is even, so the restored gamma is even.

## 4. Restoration to the retained parent

From d0 restore an integer first root tau0, then the parent's centered root is tau=2tau0-2P+k. From d2 restore an odd guard root g, and set p3=(g-1)/2. From d3 restore u with u^2=Fhalf, and set f=2u. Then f^2=F2.

The normalized multiplier maps to the ordinary parent through

    r_parent=(Delta*i-1)/2,
    (2r_parent+1)c^2=I,
    I^2=Delta*(f^2-1).

Both Delta and i are odd, so r_parent is integral. This only asserts that every new zero restores a parent zero; it does not claim every arbitrary parent ordinary multiplier is divisible by Delta.

The parent's `J3` coordinate is `J3_parent=2j`, and its unrestricted `c` coordinate is `c_parent=2c0+1`. Use V=F2(cT-R)-c. The ordinary parent auxiliary quotient is T_parent=f*T, since

    f*c*T_parent-f^2*R-c=F2(cT-R)-c=V.

From d4 recover z with z^2=delta*(Q*V^2-1). Then y=z/delta is rational and

    QV^2-(Q-1)y^2=1.

Here Q>=9, so the adjacent-coefficient rational Pell descent applies and makes y integral. The parent's last auxiliary coordinate is y_gap=y-V. Apart from the explicitly described coordinate maps, the remaining source coordinates, determinant guard and native coefficient tuple are retained.

## 5. Completeness and the actual canonical source

Completeness uses canonical source witnesses, not arbitrary parent zeros. The needed normalized odd multiplier is already supplied by the source34 coefficient theorem retained in the incoming Pell-congruences archive: `inherited/COEFFICIENT_PROOF.md`, lines 289-293, explicitly states c=psi_(a+2)(R) odd and normalized psi_(a+2)(cR)/c^2 positive odd. `inherited/SIGNED_DOMAIN_29.md`, sections on completeness with odd multiplier, proves it by the Pell binomial expansion; the ordinary multiplier is Delta times this normalized one.

The same source has q=B^N and odd N, so J is odd and 1 modulo 3, hence J=1 modulo 6. It supplies c odd and R=3 modulo 4. The squared-modulus Chebyshev reconstruction gives a positive auxiliary V with V=-c modulo f^2 and V=-R modulo c. Since f^2=1 modulo c and gcd(c,f)=1,

    T=(V+c+Rf^2)/(cf^2)

is a positive integer. This is the already proved squared-modulus construction; it requires no new conjecture about the old quotient.

For the canonical main root D=b0+H*gamma, the parity computation above forces gamma even. The sum

    tau0+gamma+4*g+8*u+16*delta*y

is odd, because tau0 is odd and every other term is even. Therefore it is 2t+1 for an integer t. Multiplying by H and adding b0 gives exactly the chosen signed sum of the five roots. The norm consequently vanishes.

These arguments establish an existence equivalence with the calibrated canonical source. They do not establish a bijection with the full seventeen-variable parent zero set.

## 6. Audit conclusion and literal verification

No mathematical gap was found in the proposed five-root composition, provided the final arithmetic graph implements the stated integer polynomials and the full inherited calibration/proof sources are retained. The old normalized source's canonical odd multiplier, rather than an unjustified division of every ordinary witness, is the key completeness dependency.

The main new mechanism is residue separation plus an affine carrier that simultaneously restores a missing congruence. The independent literal audit now verifies the direct thirteen-variable graph at exact degree 1888 with 205 binary operations. The integral midpoint shift gives an equivalent graph at exact degree 1392 with 211 operations; its cancellation-aware degree proof is detailed in `COMPACT_NORM_REVIEW.md`. Generic norm identities are checked exactly in the integer polynomial ring, and actual coefficient payloads and degree leaders are verified independently. Finite diagnostics are not substitutes for the squareclass argument or the inherited unbounded native/compiler calibration.

## 7. Unimplemented extensions discovered after the primary graph freeze

The audited primary files and operation counts above are fixed. The following observations are mathematical extensions; no alternative literal DAG, measured operation count or actual-coefficient degree certificate is supplied for them.

The normalized formula makes V odd on every integer assignment: F2 is even and c is odd. Since I is odd too, both delta=I^2-1 and r_aux=(IV)^2-1 are divisible by eight. Thus Caux=delta*r_aux is divisible by 64. This stronger unconditional fact permits smaller auxiliary-root weights.

For thirteen variables, replace the last radicand by `4H^2*Caux`; its 2-adic valuation is at least eight, preserving the five-root separation proof. Set

    Lsmall=H(2Q-1)V,
    carrier=H*(2t+(2Q-1)V)+b0.

The expression `(2Q-1)V` is odd, so this carrier still ranges over exactly the integers `H(2t+1)+b0` as t ranges over the integers. The exact identity becomes

    Lsmall^2-4H^2*Caux=H^2*V^2+4H^2*delta.

The same paired-factor argument gives degree at most 1392. The final carrier can be written with a common H factor, which suggests an operation saving, but no saving is included in the verified table.

For fourteen variables, the existing four radicands are Afirst, 4Bguard, 4F2 and 64Caux. The last may be replaced by Caux, since their radical coefficient valuations are then 0,1,2 and at least 3. A degree-reducing alternative uses last radicand `4Caux` and carrier

    2t+(2Q-1)V.

This is again an integral reparameterization of an odd carrier. With `L=(2Q-1)V`, one has `L^2-4Caux=V^2+4delta`. The first three radical weights are 17,22,9; deg L=53. The eight paired factors therefore have weighted degree at most 75, giving norm degree at most 600 and unit-product final polynomial degree at most 614 after including the retained main Pell residual of degree 14. These remain symbolic bounds and proposed variants, rather than additional measured frontier entries in this packet.
