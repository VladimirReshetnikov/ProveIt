# Independent mathematical review of the projected C222 source

Reviewed files: `agent-native/projected/PROOF_PROJECTED.md` and
`agent-native/projected/code/projected_source.py` in this shared workspace.
This is an independent AI-assisted mathematical review, not human peer
review, kernel checking, or a replay of the literal final coefficient table.

## Findings

The proposed eight-column source projection is sound in both directions.

1. The nine constructor expressions are explicitly visible, and the bundle
   conclusion does not depend on its fourth parameter. The changed bundle
   guard `g^2=d+1` is existentially equivalent over naturals to the inherited
   `g^2=(d_old+1)^2`: use `d=d_old^2+2*d_old` forward and
   `d_old=abs(g)-1` backward. Both witness maps are nonnegative where needed.
2. The local product-of-branches expression is zero exactly when at least
   one unguarded accumulator identity holds or both the bundle accumulator
   identity and its guard hold. The added two beta squares must vanish
   independently. Sharing parameters across disjuncts introduces no
   simultaneous-branch requirement; existential quantification distributes
   over the finite disjunction.
3. The independent outer bound m can be chosen after a finite proof is
   fixed. It may bound the new bundle slack g^2-1 without a circular
   requirement that the same proof length bound that slack.
4. The circuit label bound h(m)=(m+2)^4194304 is an ordinary polynomial
   with a short repeated-squaring circuit. The exponent-certificate rules
   are valid: monotonicity bounds input parameters by m, addition requires
   at most one extra exponent because m+2>=2, and multiplication adds
   exponents. The literal maximal-exponent tally is a finite audit task.
5. The carrier argument correctly orders its steps. With M=(h+1)^t,
   A(M)<((h+1)M)^t=M^(t+1). Equality A(M)=C(M), nonnegative coefficients,
   and integral leading coefficients force deg C<=t. Only then does the
   coefficient-sum bound apply. Each coefficient is strictly below M
   because the constant coefficient is 1; coefficient sum<=M alone would
   not provide strictness. Unique base-M expansion gives A=C.
6. Comparing the distinct factors 1+jX for positive j gives the Horn
   balance. If target1 were outside derivable closure, every selected
   rule with an underivable conclusion would have an underivable premise;
   counting these occurrences contradicts the extra target factor. Cycles
   and repeated premise occurrences do not invalidate this count.
7. In the converse direction, expand a finite derivation into a tree and
   successively replace an outstanding conclusion by its premises. The
   product of outstanding obligation weights is a positive integral
   accumulator from M+1 to1. Choose m after the tree is fixed. No padding
   or proof-length domination of parameter sizes is required.
8. A y larger than the accumulator entries and divisible by t! suffices
   for ordinary beta coding of t+1 entries: common divisors of two moduli
   divide an index difference<=t, and also divide y, contradicting each
   modulus being 1 modulo that divisor. The natural reconstruction
   quotients are at most x.

## Scope boundary

This review approves the new mathematical source transformation and its
carrier/CRT argument. It inherits the source calculus calibration and the
shared arithmetic representation theorems explicitly identified by the
parent packet. The endpoint counts, contraction certificates, complete
expanded polynomial, and subsequent domain-recovery conversion are separate
finite/artifact claims. No assertion of a newly compiled end-to-end formal
consistency theorem follows from this review alone.

## Frame-based domain recovery

The proposed final domain conversion uses the following previously recovered
premises, before assigning a sign to any power-certificate T or X:

- W>=2, A>=0, Z>=1;
- each power base n>0 with n<=W, its exponent k>0;
- each corresponding output m>=0, Pell ordinate Y>=0, and quotient q>=0;
- the exact frame equality A^2=1+W^3(W+2)Z^2;
- each exact identity T=2An-n^2-1 and X=Y(A-n)+m+Tq.

Under these premises the additional signs follow without a circular appeal to
power correctness. Since Z>=1,

    A^2 >= 1+W^3(W+2) > W^4.

The known A>=0 makes A>W^2, hence A>=W^2+1. Together with
1<=n<=W this gives

    A-n >= W^2+1-W > 0,
    T = 2An-n^2-1 >= 2A-W^2-1 >= W^2+1 > 0.

Thus every summand of X=Y(A-n)+m+Tq is nonnegative and X>=0. The strict
exponent positivity is not needed for this local sign argument, but it remains
needed for the inherited positive-power representation theorem. If the exact
pre-frame sign certificate establishes the listed premises for all 24 requests
and the post-frame closure establishes all 495 original variables nonnegative,
the domain conversion is mathematically sound.

For each independently guarded old variable x, the row

    x=u^2+v^2+w(w+1)

is equivalent to x>=0 over integers. Positivity follows termwise, and every
nonnegative x is represented by the three-square theorem applied to 4x+1.
The 170 such guards therefore add 510 unrestricted variables to the 495 old
coordinates. The stated 28 reversible signed monic contractions give
495+510-28=977 integer variables. Their exact occurrence/degrees and maps must
be checked by the literal certificate; they cannot be inferred merely from
this count. Every retained residual being quadratic then gives a quartic SOS.

This review verifies the frame implication and domain-conversion logic.
It does not independently rerun the pre/post-frame graph sign closure or the
28 literal signed eliminations; those are explicit finite audit obligations
handled by the root checker and the author's independent certificate checker.
