# Quotient frames recover nine signs without retaining terminal outputs

## Statement and exact source

Fix ProveIt commit `84e16e43092614bae262ca59651cb9d77e31a255`. The parent is the 75-predicate unrestricted-integer system at `Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/raw/parent.json`. Its body has 1,259 coordinates and 1,177 quadratic rows. A predicate `E >= 0` is represented by one quadratic equation

    E = a*a + b*b + c*(c+1)

in three private integer witnesses. This is equivalent to nonnegativity by the classical three-square theorem: multiply by four and use the odd square `(2c+1)^2`.

Delete the following nine scalar predicates, including their 27 private witnesses:

| Source coordinate | Name | Newly signed power output | Actual power call |
|---:|---|---:|---:|
| 548 | choose1.high | 546 | 7 |
| 575 | range0.quotient | 573 | 10 |
| 584 | range1.quotient | 583 | 12 |
| 592 | range2.quotient | 591 | 13 |
| 600 | range3.quotient | 599 | 14 |
| 609 | range4.quotient | 607 | 15 |
| 618 | range5.quotient | 617 | 17 |
| 627 | range6.quotient | 625 | 18 |
| 636 | range7.quotient | 635 | 20 |

Retain every other predicate, including `raw87 >= 2`, `raw656 >= 1`, `raw674*raw861 >= 0`, and the base-0 modulus sign `raw694 >= 0`. There are 66 predicates. Retain every original body row except row 1176.

Let `Aset` be the 43 distinct source coordinates appearing as an actual power base, exponent, or output. This set is printed in `domain.json`. Let `S` be the nine outputs in the table, and `Q` the nine removed quotient coordinates. Replace row 1176 by the single quadratic row

    W = 5 + sum(raw[i], i in Aset minus S) + sum(raw[q]^2, q in Q),
    W = raw643.

There are 34 retained power atoms and nine squared quotients. The nine outputs in S are terminal: none is an actual power base or exponent. Their magnitude will be bounded through their exact division equations, without retaining them as frame coordinates.

The original frame-only addition chain is left as dead, uniquely defined coordinates. Thus the only changed original residual is row 1176. The complete new raw system has 1,457 variables and 1,243 quadratic rows. Its equation is the sum of the squares of those rows.

**Theorem.** The new raw system has an unrestricted-integer zero if and only if the original 75-predicate system does. The supplied monic projections therefore give explicit integer quartics with the same zero-existence property. Composing with the inherited ordinary C222/refutation calibration yields

    ZFC proves: no integer zero of the supplied quartic <-> Con(ZFC).

This is an ordinary mathematical proof formalizable in ZFC. It is not a new complete Lean/Rocq proof or a printed object-language ZFC derivation. No consistency assumption is used. No global minimality is asserted.

The main supplied projection has 577 integer variables, 363 quadratic rows, 7,326 collected quartic monomials, and coefficient height 2,445,790,974,704. The lower-height companion has 582 integer variables, 368 quadratic rows, 6,069 monomials, and height 964,213. A separately preserved output-square-frame checkpoint has 586 variables and 7,059 monomials at the first height: it uses more variables but fewer monomials. Both have exact degree four.

## 1. Budget the output degree instead of storing an output bound

The old frame is `W = 2 + sum(Aset)`. It bounds every proposed output directly and therefore requires its sign before the common power proof. The new frame bounds the nine unguarded quotients by their squares and omits the nine terminal outputs. For each retained power atom a and each removed quotient q, it gives

    0 <= a <= W-5,       q^2 <= W-5,       |q| < W.

All selected bases and indices are among the 34 retained atoms. In particular their integer exponents satisfy `k<=W-5`. The five-unit offset is a degree budget for the indirectly bounded outputs. It is not an arbitrary cosmetic change.

The exact local division equations, shown below, imply `|m|<W^4` for each omitted output before its sign or power meaning is known. The product `|m| n^k` therefore still lies below `W^W`. Thus the exponent margin replaces nine direct output bounds while keeping the whole frame quadratic.

The signs and positive lower bounds used here are derived before interpreting any of the nine powers. They are not assumed from intended meaning.

The exact original prefix certificate begins with 61 semantic sign premises. The 75-predicate proof already replaces the direct sign of raw93 by the following elementary identity. Put `f=raw87`, `N=raw93`, `r=raw94`, `s=raw95`, and `C=raw91`. Original rows 78 through 85 give

    C = r+s+1,             f*C = N+s,
    N = f*r+(f-1)*s+f.

Since the retained predicates give `f>=2` and `r,s>=0`, `N>=2`. This is independent of any factorial or power interpretation.

Remove the nine quotient premises and skip exactly the old sign-inference steps whose dependencies are no longer known. The complete source checker verifies the resulting acyclic proof. Exactly 605 of the first 643 coordinates remain known nonnegative. The 38 exceptions consist of the nine omitted quotients, nine newly signed outputs, and twenty local defining gates in those quotient cones. No other actual power atom loses its sign.

All 431 original strict-positive constructor steps remain valid. In particular, all fifteen seed indices are positive. All nine selected calls have the same base

    n = raw531 = raw530+1 >= 2.

This assertion is syntactic arithmetic before any binomial or factorial meaning. The relevant radix `raw530` is positive, using the retained positive canonical modulus and the retained candidate-output bounds. The finite checker collects the whole original row identities and verifies all sign dependencies; merely observing the expected behavior on samples would not suffice.

Consequently the new frame bounds every base and exponent, all twelve other power outputs, and the absolute values of the nine omitted quotients. Because raw5 is a retained frame atom and is at least two, `W>=7`.

Here are the promised output bounds. For a range block, the exact rows give `m=M*L*q+r` and `L=r+s+1`, with retained `r,s>=0`. The canonical modulus M is at most the positive radix b: literally `b=M*(1+raw93+raw113)`, with nonnegative raw93 and raw113. Both b and L are retained frame atoms. Thus `M,L,|q|,r<W`, and

    |m| <= M*L*|q|+r <= (W-1)^3+(W-1) < W^4.

For the ninth block, the exact rows give `m=L*(C+b*q)+u`, `L=u+v+1`, and `b=C+z+1`, with retained nonnegative C,u,v,z. Both L and b are retained frame atoms; `C<b` and `u<L`. Hence

    |m| <= L*C+L*b*|q|+u
         <= (W-1)^3+(W-1)^2+(W-1) < W^4.

The sharper upper bound W^3 also follows, but W^4 is sufficient and leaves a transparent uniform argument. No sign of q or m is used in these estimates.

The old extra frame gates do not enter any power argument or logical source coordinate. In particular, the unchanged chain computing the old linear sum can now be signed; its sign is never used.

## 2. The exponential Pell bound survives

Write `A=raw644` and `Z=raw646`. The unchanged bootstrap equations give the exact identity

    A^2 - 1 = W^3*(W+2)*Z^2.

The retained base-0 modulus is

    T0 = 2*A*n0 - n0^2 - 1 >= 0,
    n0 = raw5 >= 2.

If `A<=1`, the right side is at most `-(n0-1)^2<0`. Hence `A>=2`. The new frame has `W>=2`; the bootstrap identity then forces `Z!=0`.

The pair `(A,W*|Z|)` is a positive Pell solution at center `W+1`:

    A^2 - ((W+1)^2-1)*(W*|Z|)^2 = 1.

Use the standard nonnegative Pell sequences

    chi_0(a)=1, psi_0(a)=0,
    chi_(j+1)(a)=a*chi_j(a)+(a^2-1)*psi_j(a),
    psi_(j+1)(a)=chi_j(a)+a*psi_j(a).

Positive Pell classification gives `A=chi_l(W+1)` and `W*|Z|=psi_l(W+1)` with `l>=1`. Modulo `W`, the recurrence gives `psi_l(W+1)=l`. Thus `W` divides `l`, so `l>=W`. Since `chi_l(a)>=a^l`,

    A >= (W+1)^W > W^W.

For any actual positive base `n<W`, its unchanged modulus

    T = 2*A*n-n^2-1

satisfies `T>=A`. Indeed,

    T-A = A-2 + (n-1)*(2*A-n-1) >= 0.

Every selected signed-output call therefore has `T>=A>W^W`, `2<=n<=W-5`, `1<=k<=W-5`, and `|m|<W^4`. The twelve other actual power outputs remain between zero and W. No sign of an omitted quotient is used.

## 3. Recover a signed power output from its retained ordinate sign

The following lemma is the central new step.

**Signed-output lemma.** Let `W,A,n,k,m,T` be integers with

    W>=6, A>W^W, 2<=n<=W-5, 1<=k<=W-5, |m|<W^4,
    T=2*A*n-n^2-1.

Suppose a common indexed-Pell certificate identifies

    Y=psi_k(A)>0, X=plus or minus chi_k(A),

and the actual power congruence is

    X-(A-n)*Y-m = T*h

for an integer `h`. Then `X=chi_k(A)` and `m=n^k`.

**Proof.** Put

    p=chi_k(A)-(A-n)*psi_k(A),
    q=chi_k(A)+(A-n)*psi_k(A).

The recurrence gives `p_(j+1)=n*p_j+T*psi_j(A)` with `p_0=1`, hence `p=n^k mod T`. The norm gives `p*q=1+T*psi_k(A)^2`.

If `X=-chi_k(A)`, the actual residue is `m=-q mod T`; multiplication by `p` gives

    T divides m*n^k+1.

The integer is nonzero: equality to zero would give `m*n^k=-1`, impossible because `n^k>=2`. Also

    |m*n^k+1| <= (W^4-1)*W^(W-5)+1
                  <= W^(W-1) < W^W < T.

The second inequality uses `W^(W-5)>=1`; the strict inequality uses `W>=2`. This contradicts divisibility. Therefore `X=chi_k(A)`.

Now `T` divides `m-n^k`, and

    |m-n^k| <= |m|+n^k < W^4+W^(W-5)
               <= 2*W^(W-1) < W^W < T.

Here `W>=6` ensures `4<=W-1`; `W>2` makes the last comparison strict.

Hence `m=n^k`. This also proves `m>0`. The proof does not assume that `m` is nonnegative. The hypothesis `n>=2` is essential to exclude the exceptional inverse residue `n=1,m=-1`. End proof.

The common index theorem is inherited from the signed-comparison-base proof. Its use for these nine seeds is independent of the missing signs. The retained `V>=1` and exact product `V=product(Y_i^2)*(v+1)` force all seed ordinates nonzero. The common norm gives `|U|>=A`. The comparison base obeys `B=1+4V(q4+1)` and `B=A mod U`. The exceptional `B=1` would force `U` to divide `A-1`, contrary to `0<A-1<|U|`; thus `|B|>=3`. The signed-B index theorem allows the remaining comparison coordinates and quotients to have either sign.

For each of the nine selected seeds, the literal old guard `Y-k>=0` is still present. Since `k>=1`, its actual ordinate is positive. The inherited short-interval theorem yields `Y=psi_k(A)` and `|X|=chi_k(A)`. The nine calls are precisely calls 7, 10, 12, 13, 14, 15, 17, 18, and 20. Their base is raw531, so the signed-output lemma applies to every one. No interpretation of the four seeds whose index guards were removed in earlier research is required to perform this step.

## 4. Recover eight range quotients

For each of the eight range blocks, the exact original rows reduce to

    m = M*L*q+r,
    L = r+s+1,

where `M=raw129>=1` is the canonical modulus, and the retained guards give `r,s>=0`. Therefore `L>=1` and `0<=r<L<=M*L`.

Section 3 has just proved `m=n^k>0`. If the integer `q` were negative, `q<=-1` and

    m <= -M*L+r < 0,

a contradiction. Thus `q>=0`. This recovers all eight deleted range predicates at their original source values, without assigning a new quotient or changing the source arithmetic.

The exact bindings `(q,m,L,r,s)` are

    (575,573,574,576,577), (584,583,574,585,586),
    (592,591,574,593,594), (600,599,574,601,602),
    (609,607,608,610,611), (618,617,608,619,620),
    (627,625,626,628,629), (636,635,626,637,638).

The checker eliminates all local defining gates and compares every coefficient of these division and remainder-bound identities against the literal original rows.

## 5. Recover the ninth high-digit quotient

For `q=raw548`, write

    m=raw546, L=raw547, C=raw111, b=raw530,
    u=raw549, v=raw550, z=raw551.

The original rows give

    m = L*(C+b*q)+u,
    L = u+v+1,
    b = C+z+1.

The retained signs give `u,v,z>=0` and `C>=0` before any binomial meaning. Therefore `L>=1`, `0<=u<L`, and `0<=C<b`. Section 3 gives `m>0`. If `q<=-1`, then

    m <= -L*b+L*C+u
      <= -L*b+L*(b-1)+(L-1)
       = -1,

a contradiction. Hence `raw548>=0`. This recovery uses the literal digit and remainder bounds, not an assumption that `C` is already a binomial coefficient.

With these nine signs recovered, the original 643-coordinate prefix sign proof is fully available again. Fresh three-square guard witnesses can be supplied for every recovered predicate. The arithmetic body values have not changed up to this stage.

## 6. Complete the twelve remaining powers, without a false global bound

At this point all nine omitted quotients are nonnegative and all 643 prefix coordinates have their original nonnegative signs. The new W need not exceed the old linear frame. The nine selected outputs need not be smaller than W. Neither statement is asserted or used.

The nine selected powers already have their exact intended values, by the new signed-output lemma. The remaining twelve calls are precisely

    0,1,2,3,4,5,6,8,9,11,16,19.

Their bases, exponents, and outputs are retained frame atoms and are therefore nonnegative and less than W. For those calls the existing power/index arguments retain every original numerical bound. The earlier 75-predicate proof's special local factorial argument uses calls 1,5,6; its parity argument uses calls 0,2,9. All are among the twelve bounded calls. None of those arguments uses a quotient or terminal output from the nine deleted cones.

The common bootstrap and signed-comparison-base theorem are unchanged. Their index classification does not depend on the magnitude of a proposed power output. A seed selected by one of the nine new calls has already been oriented by Section 3. A seed selected by one of the twelve other calls is oriented by the inherited bounded-output argument. The omitted K/shifted-K and t/k122 index slacks are recovered in exactly the prior staged order, with all their required core outputs still bounded by W.

Thus every one of the 21 actual power calls is correct at the current arithmetic source tuple. The subsequent factorial, binomial, CRT-range, and logical compilation arguments use these exact power values, not their magnitudes relative to the private W. The private frame does not enter the logical arithmetic at all.

This selective composition is essential. It would be invalid to apply an old theorem requiring every output below W without supplying the new signed-output argument for the nine excluded outputs. The finite source checker certifies that all required core-call atoms remain framed; the ordinary proof is the case split above.

## 7. Both directions require rebuilding private Pell witnesses

The following construction gives the precise nonpointwise existence map. It is a finite standard Pell/CRT construction for any fixed finite tuple of genuine powers, and works with either admissible frame.

Keep all logical/arithmetic source values below raw643. Choose the desired frame `W_*` as either the old linear frame or the new quotient-square frame. All source power bases and exponents lie strictly below `W_*`. In the old frame all outputs do as well. In the new frame this is required only for the twelve retained outputs; it is not required for completeness of a genuine power. Set

    A_* = chi_(W_*)(W_*+1),
    Z_* = psi_(W_*)(W_*+1)/W_*.

The quotient is a positive integer by the recurrence modulo W_*. Set the bootstrap free coordinate to `Z_*-1`. For each of the fifteen actual seed indices k_i, choose

    X_i=chi_(k_i)(A_*), Y_i=psi_(k_i)(A_*).

The one derived t+1 pair is supplied by the literal Pell addition recurrence. Every seed ordinate satisfies `Y_i>=k_i>=1`.

Choose a common unit. Let `L0=4*product_i(Y_i^2)` and consider the invertible element `A_*+s` in the finite ring

    (Z/L0 Z)[s] / (s^2-(A_*^2-1)).

Its inverse is `A_*-s`, so a positive power equals one. Taking the corresponding positive Pell coordinates gives

    U=1 mod L0, V=0 mod L0, U>0, V>0.

Then `gcd(U,4V)=1`. CRT supplies B with `B=A_* mod U` and `B=1 mod4V`; increase B along this progression until all desired quotient representatives are nonnegative. In particular B>A_*, `q4=(B-1)/(4V)-1>=0`, and the source's common product multiplier is nonnegative.

For each seed, set `S_i=chi_(k_i)(B)` and `R_i=psi_(k_i)(B)`. Polynomial recurrence and the two base congruences give

    S_i=X_i mod U,       R_i=k_i mod4Y_i.

Choose the corresponding integer quotient witnesses. The exact source power congruence has an integer quotient because its output is the genuine power `n^k`. Also `n^k<W_*^W_*<A_*<=T`, even if the output exceeds W_*. Assign it accordingly. Reevaluate every private topological defining gate and the old dead frame addition chain. Every private norm, congruence, index equation, and frame equation now holds.

Every body predicate of either source has the required sign: semantic prefix signs have been retained or recovered; seed slacks are nonnegative; V-1 is nonnegative; the product of the two selected index slacks is nonnegative; and f-2 is unchanged. Choose fresh three-square witnesses in the required private positions. These witnesses need not equal their previous values.

Starting with a new 66-predicate zero, Sections 1 through 6 provide genuine power semantics and all prefix signs. Apply this construction using the old linear frame to obtain an original 75-predicate zero.

Starting with an original 75-predicate zero, its inherited ordinary proof provides genuine powers and prefix signs. Apply the same construction using the new quotient-square frame and only the 66 retained predicates to obtain a new zero.

These maps establish zero-existence equivalence. They do not assert a zero-set bijection, preservation of Pell witnesses, or equality of the two frame values. Monic coordinate projections *do* give exact polynomial inverse maps between each projected equation and its own raw parent; that separate fact is certified by `projection.json`.

## 8. Connection to ZFC and verification boundary

The source arithmetic is the direct C222 proof-certificate construction. The inherited coefficient recipe and ordinary arithmetic compilation occur in the pinned `ConZFC_407_888_Quartics_2026-10-24.zip`, followed by the documented candidate-output factorial-radius and signed-source transformations. The immediate logical bridge is the unconditional theorem

    KEndpoint.c222_iff_zf_refutation:
      KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot,

followed by

    ConstructibleChoice.zf_refutation_iff_zfc_refutation.

The first theorem precedes the machine-parameter section in its source. This route does not encode or simulate K215, although historical source modules may import machine-related declarations for their other results. The ordinary calibration uses first-order completeness and the constructible model argument to relate ZF and ZFC refutability. It must not be confused with using the bare existence of an external Lean theorem as a finished internal-ZFC proof object.

The inherited ordinary proofs and this transformation use finite arithmetic, induction, Pell classification, finite rings, CRT, and the standard syntactic calibration. All arguments can be carried out inside ZFC over its internal natural numbers. They do not quantify only over externally standard certificates, assume Con(ZFC), or assume arithmetic soundness. Composing them proves the displayed equivalence with the repository's fixed syntactic consistency predicate.

The executable checks have a narrower, precisely stated role. They verify the entire frozen source boundary; all retained predicates and private witness positions; the changed quotient frame row; the filtered acyclic sign proof; the exact division interfaces and polynomial magnitude bounds; all relevant whole original-row identities; every monic projection and its integer inverse; and every coefficient of the expanded quartics. They do not replace the unbounded lemmas above or assert that the equation has no solution. The source and projection checks remain active under Python optimization.
