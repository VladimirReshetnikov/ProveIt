# A radix-compatible canonical scale and its packed-marker obstruction

Root suggested replacing the excluded scale `q=2*3^k` by `q=B*3^k`
for a fixed authentic compiler radix `B=2^d`. This works at the stated
scalar interface: for every such compiler there are infinitely many even
nondyadic q satisfying its literal repunit equation, the exact canonical
cubic divisibility `q^3 | Y_R`, and both retained numerical bounds on R.
Every positive member of the progression below works; no additional
asymptotic threshold is needed.

The literal packed-index equation imposes a further obstruction: its
forced marker is too large for the already-proved nonnegative outer
coordinate C. Section4 excludes every member of this new family at
that stage. Thus the isolated repunit obstruction is removed, but no
positive direct-X83 zero or improved universal bound follows.

## 1. Fixed constants, progression and theorem

Fix an odd integer d>=3 and put B=2^d. The inherited original compiler
radices meet this premise: their exponents are powers of5 and in fact
divisible by25. Define

    m = B-1,
    c = 2^(3d+1),
    o = ord_m(3),
    L = lcm(o,c).

Here gcd(3,m)=1 because d is odd: B=-1 modulo3 and m=1 modulo3.
Thus the unit order o exists. These are fixed positive integers depending
only on the chosen compiler radix. They are proof parameters, not newly
supplied source ports or uncharged additions to a paid circuit.

For every positive integer n take

    k = n*L,
    e = 3k+c,
    q = B*3^k,
    R = 2*3^e-3,
    r = (R-1)/2,
    X = 2^R,
    Y_R = (1/2)*sum_(j=0)^r binom(2r,r+j)*X^j,
    J = (q-1)/(B-1).                                      (1)

Then Y_R and J are positive integers and

    q is even and nondyadic,       q >= B,
    q = (B-1)*J+1,                 J is odd,
    R = 3 modulo4,
    v3(Y_R) = 3k+c-1 >= 3k,
    v2(Y_R) >= 3d+2,
    q^3 divides Y_R,               q does not divide X,     (2)

and

    (2q-1)*(q^2-1) < R < q^3*(q-1).                        (3)

An explicit computable first admissible exponent is **k0=L**. Computing
the finite unit order, an integer lcm, and a power of2 defines that
threshold; its size is not claimed efficient. No q, R, X or Y of an
authentic compiler instance is numerically materialized in this packet.

## 2. The repunit and prime-power scale conditions

Since k is divisible by o, `3^k=1 modulo m`. Also B=1 modulo m.
Therefore q=1 modulo m, proving J is an integer. It is positive because
q>B, and odd because both q-1 and m are odd. Clearly v2(q)=d and
v3(q)=k>0, with no other prime factors. In particular q does not divide
the pure power X of2.

The previously proved all-size canonical valuation theorem states

    v3(Y_(2*3^e-3)) = e-1, for every e>=1.                   (4)

Its proof controls every term after an exact expansion about X=-1;
it is a theorem about the whole half-binomial, not an estimate on its
central coefficient alone. Applying (4) gives the claimed 3-adic depth.
Since c>=1, this depth is at least3k.

For the binary depth, c divides both k and e. In particular e is even
and `v2(e)>=3d+1`. The elementary lifting identity for even e gives

    v2(3^e-1)=v2(3-1)+v2(3+1)+v2(e)-1=2+v2(e),
    v2(R+1)=3+v2(e)>=3d+4.                                (5)

Consequently the lowest 3d+4 binary digits of the positive integer R
are all1, and its population satisfies `pc(R)>=3d+4`.

For completeness, the exact binary identity at every odd R>=3 is

    v2(Y_R)=pc(R)-2.                                       (6)

Indeed the central summand `binom(2r,r)/2` has valuation `pc(r)-1`.
Every noncentral summand has valuation at least R-1, strictly greater
than that central depth. The constant term therefore cannot cancel.
Since R=2r+1, `pc(R)=pc(r)+1`, proving (6). Equations (5)--(6) yield
`v2(Y_R)>=3d+2`, which is stronger than the required3d. Together with
(4) and the prime factorization of q this proves `q^3 | Y_R`.

## 3. Exact numerical outer bounds and the explicit threshold

Put the fixed positive rational number

    Gamma = 2*3^c/B^3.

Direct substitution gives

    R = Gamma*q^3-3.                                      (7)

We have c>3d, hence `3^c>2^(3d)=B^3` and Gamma>2. Also L>=c and
k>=L, so k>=c. Therefore

    q/Gamma = (B^4/2)*3^(k-c) >= B^4/2 >= 8.

As Gamma>2, this implies `q>Gamma+1`. In particular, the first allowed
exponent k=L already exceeds every required numerical cutoff. The exact
differences from the desired endpoints are

    R-(2q-1)*(q^2-1)
      = (Gamma-2)*q^3+q^2+2q-4 > 0,

    q^3*(q-1)-R
      = q^3*(q-1-Gamma)+3 > 0.                            (8)

This proves (3) for every n>=1, not merely eventually. Distinct n give
distinct q, so the family is infinite for each fixed admissible B.

## 4. The packed marker excludes every member

The actual modified mask has `MC` even and `0<MC<B-1`. In particular
`2<=MC<=B-2`. The authentic positive-zero bootstrap, before input
decoding, gives the following necessary outer conditions:

    F,Z,alpha,x,J > 0,        C >= 0,
    U=q-F=C+Z+alpha+2d*x,
    R=(q*U-Z)*(q^2-1)+(MC+q*MF_source)*J,             (9)

where `MF_source>0`. These conditions alone are incompatible with (1).
No mask interpretation or full parent soundness theorem is needed.

First, `U>Z` and `F>0` give `0<Z<q`. The prescribed R also has the
following exact representative modulo q:

    R = 2*3^k-3 modulo q.                           (10)

To prove (10), subtract its proposed right side. The difference is
`2*3^k*(3^(e-k)-1)`. Here `e-k=2k+c` is divisible by c and is even.
The same elementary lifting formula as before gives
`v2(3^(e-k)-1)>=3d+3`, hence B divides twice that quantity. Since
`q=B*3^k`, the difference is divisible by q. Also
`0<2*3^k-3<q`.

Reducing (9) modulo q now yields

    Z = 2*3^k-3-MC*J modulo q.

The displayed right side is negative: since MC>=2 and
`J=(B*3^k-1)/(B-1)`, we have `MC*J>=2J>2*3^k`.
Adding q gives the strictly positive quantity

    Z_*=(B-1-MC)*J+2*3^k-2.                       (11)

It is less than q because the preceding representative was negative.
As `0<Z<q`, there is no freedom to select a different lift:

    Z=Z_* > 2q/B-2.                                (12)

On the other hand, positive masks and `U>Z` in (9) imply

    R > (q-1)*Z*(q^2-1) > (Z/2)*q^3.              (13)

The second strict inequality holds for q>=3: after doubling and
subtracting q^3 its coefficient is
`q^3-2q^2-2q+2 = q^2(q-2)-2q+2 > 0`.
Using `R=Gamma*q^3-3`, equation (13) forces `Z<2*Gamma`.
But Section3 gives `q/Gamma>=B^4/2`, so (12) instead forces

    Z > Gamma*B^3-2 > 2*Gamma,                     (14)

where the last inequality uses B>=2 and Gamma>2. This is the required
contradiction. Every member is therefore excluded by the exact packed
index together with the nonnegative-C bound, already before the
canonical input, transport or native masks are interpreted.

**Corollary (root's broader fixed-offset marker bound).** The same outer
premises give a finite cutoff without the special lcm progression. Fix
any nonnegative integer c_* and put

    q=B*3^k,  e=3k+c_*,  R=2*3^e-3,
    Gamma_*=2*3^(c_*)/B^3,  k>=1.

If the repunit equation and (9) hold, necessarily

    q < B*((B-1)*(2*Gamma_*+3)-MC)
      < B*(B-1)*(2*Gamma_*+3).                     (15)

Indeed e>=k, so modulo3^k we have R=-3, while (9) gives
`R=Z+MC*J` and the repunit gives `(B-1)J=-1`. Multiplying yields

    (B-1)*(Z+3)-MC = 0 modulo3^k.

The left side is strictly positive because Z>0 and0<MC<B-1.
It is therefore at least3^k=q/B. Thus

    Z >= q/(B*(B-1))-3+MC/(B-1).

The argument in (13), which needs no Gamma>2 assumption, still gives
`Z<2*Gamma_*`. Combining these inequalities proves the strict bound
(15). Its right side is fixed, so only finitely many k can satisfy
these necessary conditions for each fixed c_*. This corollary does not
exclude unbounded changes of e-3k and does not assume cubic divisibility
or any particular input. Root supplied this generalization during the
independent challenge; I checked the congruence and strict inequalities.

## 5. Exact compiler boundary and retained failures

The authentic direct-X interface keeps B fixed and requires
`q=(B-1)J+1`. Equation (2) really satisfies that same equation, with a
positive integer J. It does not replace B by another radix. The earlier
31/601 conflict excluded `q=2*3^k` for25|d; it does not apply to (1):
the new multiplier B is1 modulo B-1, so the required congruence becomes
`3^k=1`, exactly the one enforced here. There is no contradiction with
the frozen earlier exclusion.

**Review remark 1 (a retained false transfer is still false).** The
earlier inference from canonical cubic divisibility and numerical
outer bounds to a full compiler zero was refuted by the repunit
obstruction for `q=2*3^k`. The present family satisfies the missing
repunit equation but does not validate that inference in general.
Conditions (2)--(3), including the repunit, do not suffice: the explicit
contradiction in Section4 refutes that stronger inference for this new
family as well.

**Review remark 2 (the preliminary completion question is resolved).**
The first draft asked whether members of (1) could also satisfy the
literal packed-index and canonical input/transport conditions. Section4
answers that question negatively for every member; no such positive
outer completion exists. Its proof only uses C>=0 and does not assume
the stronger decoded identity `C=Z+2^(2d*x+b)`.

**Review remark 3 (root's correction of a draft identity).** The first
draft wrote the lower-endpoint difference in (8) with constant term -3.
That right side exceeds the actual difference by exactly1; the correct
constant is -4. For example q=2 and Gamma=3 give R=21 and difference12,
whereas the erroneous right side gives13. The example tests the stated
polynomial identity, not an authentic compiler tuple. Root identified
this error before freeze. The corrected expression remains strictly
positive for q>=2 and Gamma>2, so no theorem conclusion changes.

**Open question 1.** A different relation among q and the canonical
index R would have to avoid both the excluded `q=2*3^k` repunit and
the forced-marker contradiction above. No conclusion is made here
about all canonical nondyadic scales or the full direct-X83 soundness
question. The earlier resonant transport repair remains a separate
necessary-and-sufficient result within its expressly restricted class.

## 6. Provenance, attribution and evidence limits

Root proposed the replacement `q=B*3^k`, the choice c, and the lcm
progression. This note independently derives the prime-power bounds,
proves that k0=L suffices without an additional tail restriction, and
derives the new packed-marker contradiction.
The exact three-adic valuation (4) is inherited from the frozen and
committed author note
`direct_X_canonical_three_adic_family_pascal.md`, SHA256
`c18f09aa7fd0b4eb89bbdbbca2a5b5ad3aed3f5d559e6afb02034cb9bb62f7cc`,
read in full as inert text. The full canonical interface note
`direct_X_canonical_resonance_repair_aristotle.md`, SHA256
`addf7b16329a70f002478895295e5979f1b0561f9b1962cfe3bafc9cd467f1e9`,
was also read in full. The actual fixed-radix recipe in
`complete75_half_binomial_compiler.md`, lines1--70, was read to bind
the odd power-of-five exponent hypothesis. Its whole-file SHA256 is
`68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.
The proof of25|d remains in the first frozen note; this result only
needs odd d>=3. For (9), `direct_X_authentic_outer_root.md`, lines1--49,
was read inertly; its whole-file SHA256 is
`35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617`.
The nonnegative-C conclusion there is a pre-input bootstrap consequence,
so its use in Section4 does not assume a completed canonical input.

Any new evidence accompanying this note is restricted to fresh small
modular-order and lifting controls at explicitly synthetic widths,
plus byte/read-span authentication. It does not materialize gigantic
radices of an actual compiler, canonical X/Y, Pell witnesses or source
zeros. No frozen, predecessor, supplied or archived program is run or
imported; no saved source array is evaluated; no repository or Git
mutation occurs. The proof above supplies the all-size claims.

The final fresh controls cover four exact small unit orders and16 modular
progression cases at synthetic d=3,5,7,9, including the residue needed in
(10). Their largest modulus is2^34. A separate33 generic scalar checks
verify the corrected polynomial identity in (8) and its retained
off-by-one boundary; these are not members of the proposed family.
Normal and optimized (`-O`) executions before freeze produce identical
receipts. The helper SHA256 is
`26ee2ed46aefece988cdfffad89e5f4f4f4e25703fca93e43b6d090c6a0b8a99`.
The receipt binds this note and records root's exact correction; its
own hash is supplied separately to avoid a circular hash declaration.
