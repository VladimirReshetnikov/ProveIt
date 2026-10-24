# Refinement: the candidate factorial's square supplies its own radius

For every pair of nonnegative integers n,F, define

    C=binom(F^2+n,n), N=(F^2+1)^n.

Then the following exact fixed-point characterization holds:

    F=ceil(N/C)  if and only if  F=n!.

In particular the radius does not need to include the argument n.
This improves the initially audited radius n^2 F to F^2.
The fixed-point characterization is proved below, including every small n.

## Proof of soundness

Write K=n! and, for R>=0,

    f_n(R)=(R+1)^n/binom(R+n,n)
          =K product_(j=1)^n (R+1)/(R+j).

This is positive, at most K, and nondecreasing in R. For n>=2 and R>0,
the same elementary product bound as in the initial audit gives

    0 <= K-f_n(R) < K n(n-1)/(2R).                 (1)

A satisfying output F cannot be zero, since f_n(F^2)>0.

Suppose first that n>=4. Since F>=1, monotonicity gives

    f_n(F^2) >= f_n(1) = 2^n/(n+1).

For every n>=4, the elementary inequality2^n>n^2-1 follows by
induction. Its base is16>15. If it holds at n>=4, then
2^(n+1)>2n^2-2>(n+1)^2-1 because n^2-2n-2>0.
Thus2^n/(n+1)>n-1, and F=ceil(f_n(F^2))>=n.
Applying (1) with R=F^2 now gives

    K-f_n(F^2) < K n(n-1)/(2F^2) < K/2.

Thus f_n(F^2)>K/2 and F>K/2. Apply (1) again:

    K-f_n(F^2) < 2n(n-1)/K <= 1,

because K/[n(n-1)]=(n-2)!>=2. Since f_n(F^2)<=K and K is an
integer, its ceiling is K, and F=K.

For n=0,1 the quotient is exactly1. For n=2, its ceiling is at most2,
and F=1 gives quotient4/3, so F=2. For n=3, the ceiling is at most6;
for F=1,2,3,4,5,6 the exact quotients and ceilings are:

| F | f_3(F^2) | Ceiling |
|---:|---:|---:|
| 1 | 2 | 2 |
| 2 | 25/7 | 4 |
| 3 | 50/11 | 5 |
| 4 | 289/57 | 6 |
| 5 | 338/63 | 6 |
| 6 | 1369/247 | 6 |


Only F=6 is a fixed point. These small cases are exact rational
computations, not numerical approximations.

## Proof of completeness

Take F=K. For n>=2, (1) gives

    0 <= K-f_n(K^2) < n(n-1)/(2K)
                    =1/[2(n-2)!] <=1/2.

Its ceiling is therefore K. For n=0,1 the quotient is1 as above.
This proves the biconditional for every n>=0.

## One square radius serves a whole bounded family

Suppose the first requested factorial argument is H and every subsequent
argument n satisfies0<=n<=H. Use a single shared radius

    R=F_H^2.

The first fixed-point certificate forces F_H=H!. For every subsequent
n>=2, formula(1) gives

    0 <= n!-f_n((H!)^2)
       < n! n(n-1)/(2(H!)^2)
       <= H(H-1)/(2H!)
       =1/[2(H-2)!] <=1/2.

For H>=4, the last bound improves to1/4. The bound only concerns n>=2,
so H>=2 whenever the factorial(H-2) notation is used.

The n=0,1 cases remain exact. Hence each subsequent ceiling certificate
forces its own output to be n!. The reverse implication uses the genuine
factorials and the same radius. No extra radius power needs to be
certified.

## Polynomial realization and cost

The nonnegative rows

    N+C=C F+r+1,
    C=r+s+1

still encode the ceiling exactly. Replacing the first radius computation
n^2 F by F^2 removes one multiplication gate and its stored wire in the
inspected arithmetic compiler. It introduces no new unknown, inequality,
nonpolynomial operation, or power/binomial call.

In the actual consistency compiler the first argument H is already at
least5, so the main bootstrap uses only the uniform n>=4 proof; the small
cases above make the reusable lemma total. The order of semantic witness
construction is unchanged: choose the actual factorial values, then the
radius, binomial values and common radix, then power outputs, and finally
the shared Pell frame.

This is an ordinary arithmetic proof. The accompanying independent regression script checks2,648 exact fixed-point
cases through n=12, including factorial neighbors, and91 shared-radius cases.
These finite diagnostics are not the proof.

## Universal arithmetic-frame boundary

The deferred binomial implementation computes its coefficients by radix
digits of powers. Its correctness is universal for supplied natural upper
and lower arguments, using a radix strictly larger than2^upper; it does
not assume the intended factorial output. The shared Pell power frame
also has a universally quantified correctness theorem for every positive
base/exponent/output tuple satisfying its rows. Neither theorem may be
proved by assuming the bootstrap output is already correct.

For soundness these universal arithmetic interfaces are applied first,
then the fixed-point theorem above identifies the output. Their input
positivity is already known: F is nonnegative, so R+1=F^2+1>=1 before
F is identified; every actual exponent is H or t, hence positive. Also
R+n>=n implies C=binom(R+n,n)>0 independently of F's intended value.
The zero-F branch is excluded only afterwards by the ceiling rows and
positive N. This ordering avoids a hidden precondition cycle. For completeness
the actual factorial outputs and semantic binomial and power values are
chosen first; a sufficiently large shared Pell frame is chosen last. The
new radius therefore creates no unresolved circular semantic dependency.
