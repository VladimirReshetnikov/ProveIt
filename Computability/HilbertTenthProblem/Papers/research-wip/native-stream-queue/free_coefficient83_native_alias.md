# Free-coefficient native index mismatch, and a four-bit mask obstruction

This bounded note strengthens the unresolved boundary of the [free-coefficient83 scout](complete83_free_coefficient_scout.md). Its scaled first/main subsystem can be extended to the first-index equation and both free-coefficient auxiliary factors while the main Pell index p differs from the supplied native target R. Thus the missing divisibility cannot be replaced simply by those native equations.

The same family, however, cannot satisfy the necessary four-bit compiler-mask conditions for **any q=16^k**. There is no full positive candidate zero, false accepted ordinary input, or new universal operation bound claimed here. The input and transport equations remain outside the construction. R is an abstract native target until packing is checked; in the complete circuit it is the computed register `r_lhs`, not a supplied coordinate.

The [helper](free_coefficient83_native_alias.py) and [receipt](free_coefficient83_native_alias.json) authenticate the frozen 83 packet and preceding scaled-first-index proof as data. They execute no predecessor Python or historical suite. The current 83 source and its review are unchanged.

## 1. Scaled first/main data with a restored positive h

Use the proven family from [the earlier scaled obstruction](first_index_scaled_obstruction.md): for odd t≥11, put

    p=t(t+2), n=t(t+1), X=2^p, Y=2^(t+1),
    E=XY, a=Y(X+1), A=a+2, Delta=A²−1,
    P=2XY²+1,
    (D,c)=(chi_A(p),psi_A(p)),
    (tau,k)=(chi_P(n),2psi_P(n)).

That proof establishes the exact first/main Pell equations, the strict ratio `kY<c<k(Y+1)`, and a positive integer

    gamma=(D−ac−X)/(4a+3)>1.

Set eta=c−kY, zeta=k−eta, rho=1 and sigma=gamma−1. All are positive and restore the literal main-root expression. The source scales hold at q=16 using w=2^(p−4), s=2^(t−11). They also hold at q=16^k whenever the corresponding exponents p−4k and t+1−12k are nonnegative. The earlier large-rank bounds remain valid.

Now choose a different abstract target:

    R=2n−1,   R−p=t²−1>0.                            (1)

Since P=1 modulo E, `psi_P(n)=n modulo E`. Consequently

    h=(k−R−1)/E=(k−2n)/E                             (2)

is an integer, and it is positive because n>1 and P>1 imply psi_P(n)>n. Thus the actual first-index factor `k−hE−R` equals 1. No index equation was deleted in this construction. It is main index recovery, p=R, that will fail after freeing the coefficient.

## 2. Conditional auxiliary extension at the wrong index

Here p is always 3 modulo 4. Put

    f=D, S=Delta*c.

Then `Delta*f²−S²=Delta`. Choose a positive auxiliary index v satisfying

    v=R modulo c,  v=p modulo 4p.                    (3)

Since c is odd, these congruences are compatible exactly when

    gcd(c,p) divides R−p.                            (4)

This is a genuine condition, not an assertion for every odd t. For this family,

    gcd(p,R−p)=gcd(t(t+2),t²−1)=gcd(t+2,3),           (5)

so (4) is equivalently `gcd(c,p)|gcd(t+2,3)`.

For a compatible v, let

    V=chi_S(v)/S, y=psi_S(v).

Because v is odd, V is a positive integer. Since v=p modulo 4p, it is 3 modulo 4. The same odd-quotient polynomial identities used in the frozen 83 scout give

    V=−v=−R modulo c.

For the other congruence, the Pell unit at index 2p is (−1,0) modulo f=D, so its index-4p value is (1,0). Therefore `psi_A(v)=psi_A(p)=c modulo f`. As `S²=Delta*(f²−1)`, odd-quotient reduction gives

    V=−c modulo f.

The main equation gives gcd(c,f)=1 and f²=1 modulo c. Hence

    T=(V+c+R*f²)/(c*f)                               (6)

is a positive integer, and the actual Bezout expression satisfies

    V=c*(Tf−1)−R*f².

The auxiliary Pell equation is

    S²*V²−(S²−1)*y²=1.

Thus the first, main, index and auxiliary factors are 1, and the scaled strong factor is Delta, with the strict ratio, positive main projection and asymmetric scales intact, yet p≠R. This statement does **not** include the input or transport factors. The original integer inverse would still require i=S/(Delta*c²)=1/c, so the old strong-rank theorem cannot be applied.

## 3. Bounded exact and modular evidence

The fresh exact first/main fixture t=11 has

    p=143, n=132, R=263, X=2^143, Y=2^12.

Its c has 22,153 bits and h has 21,986 bits. The receipt stores the complete first/main fields and a CRT auxiliary index as hexadecimal integers. It verifies both norm equations, both positive ratio gaps, the main projection, positive integral h, large-rank inequalities and the exact period/CRT conditions. V,y,T are defined by the proof and are not expanded into enormous integers.

To test (4) at larger t, the helper computes c modulo p by modular Pell powering. It does not construct c. Selected results are:

| t | p | R | c modulo p | gcd(c,p) | Compatible |
|---:|---:|---:|---:|---:|---|
|11|143|263|87|1|yes|
|13|195|363|0|195|no|
|17|323|611|284|1|yes|
|65|4355|8579|584|1|yes|
|71|5183|10223|851|1|yes|
|83|7055|13943|1410|5|no|

The full receipt records twenty declared cases, not a census. At t=65 and 71, R also lies inside the positive q=16 packing interval `7905<R<61440`. Interval membership alone does not establish the packing identity or a valid mask recipe.

## 4. Uniform obstruction from the four-bit necessary masks

Assume now the actual repunit and packing forms with B=16:

    q=15J+1,
    R=(q²−Z−qF)(q²−1)+(MC+q*(MF0+15))*J.              (7)

The necessary mask conditions considered here are

    0<MC,MF0<15,
    MC=2 modulo 4, MF0=4 modulo 8,
    pc(MC)+pc(MF0)=4.

They leave exactly

    (MC,MF0)=(6,12),(10,12),(14,4).                   (8)

These conditions alone do not certify a complete admissible fixed-program recipe. The conclusion below is already an obstruction at this weaker arithmetic interface.

Since q divides X=2^p and q≥16, q is a positive power of 2. Its required congruence q=1 modulo 15 forces the exponent to be a multiple of 4: the order of 2 modulo 15 is 4. Thus q=16^k for an integer k≥1. Modulo 17, q=(-1)^k and q²−1=0. Also J=(q−1)/15 is 0 when k is even and 1 when k is odd.

If k is even, (7) gives R=0 modulo 17, hence 2R+3=3 modulo 17, a nonsquare.

If k is odd, (7) gives

    R=MC−MF0+2 modulo 17.

For the three masks in (8), the residues of R are respectively 13,0,12, so the residues of 2R+3 are 12,3,10. All are nonsquares modulo 17. But the chosen target (1) always satisfies

    2R+3=(2t+1)².                                   (9)

This is a contradiction for every k, every F,Z, and every t in the family. The proof uses neither an unproved native decoding theorem nor a bounded search over q. The helper checks the three exact mask possibilities, both parity cases of k and all square residues modulo 17.

## 5. What this changes, and what remains open

The scaled native equations do not recover p=R after the coefficient deletion, even when the first-index quotient h is a positive integer. That is a stronger obstruction to the old native proof route than merely showing nonintegrality of the original i.

The explicit family nevertheless cannot provide a full counterexample on the B=16 necessary-mask interface, for any repunit scale consistent with its dyadic X. The input and transport constraints have not been supplied either. Other bases, other native families, and the divisor/sign branches of a generic product-equals-Delta zero remain separate obligations. This note neither proves nor refutes ordinary-input soundness of the 83-operation candidate.

Replay from any directory:

    python3 free_coefficient83_native_alias.py --root ABS_WIP --expect free_coefficient83_native_alias.json

Before installation of the unchanged 83 scout, add `--scout-root /tmp`. `--output PATH` writes the deterministic receipt. All checks are explicit exceptions and recursively type-exact, including under optimized Python. No giant complete compiler zero or new complete polynomial is emitted by this evidence packet.
