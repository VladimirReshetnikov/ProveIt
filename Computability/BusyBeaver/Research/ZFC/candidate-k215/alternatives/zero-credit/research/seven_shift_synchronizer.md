# Seven-shift synchronization for the scratch-biased 215-state scheduler

This is a new ordinary mathematical proof about an ABSTRACT scheduler. The historical scratch-biased transition table DOES NOT implement the parser equations below: its unchanged CC3 return lands at dispatch rather than the scheduler root, and a valid all-truth frame has a finite false halt. The present theorem is a specification-level result for a future corrected implementation. It is not a calibration of that table. See scratch_transfer_audit.json for the concrete counterexample.

Let `P(a,b)=(a+b)(a+b+1)/2+b` and let `f(n)` be its right projection. A raw candidate code `n` is parsed without decrement on its first command. At a positive continuation `L`, the next raw code is `L-1+b`, where `b=0` after S and `b=1` after MP or AX. The command tags are S=0, MP=1, AX>=2. Therefore, ignoring semantic halts, the finite word `W(n)` obeys:

* `unpair(n)=(0,y)`: S, then `W(y-1)` if y>0; otherwise stop.
* `unpair(n)=(1,y)`: MP, then `W(f(y))` if f(y)>0; otherwise stop.
* `unpair(n)=(a,y)`, a>=2: AX, then `W(f(f(y)))` if f(f(y))>0; otherwise stop.

All recursive arguments are strictly below n. Let `e(n)` be 0 if the last command of W(n) is S, and 1 otherwise. This is a primitive recursive syntactic function, independent of the work-register values.

## Exact delayed candidate sequence

If launched candidate numbers are n_0,n_1,... and b_* is the bias at the first refill, then

    n_1 = n_0+1+b_*,
    n_(j+1) = n_j+1+e(n_(j-1))  (j>=1).

The one-command delay is essential: the next counter was incremented at the beginning of the current candidate using the preceding candidate's last-command bias. Every step is 1 or 2. Every candidate finishes syntactically by strict descent unless a semantic halt has already occurred.

## Forced-hit lemma

Suppose the first launched candidate is n_0, that k>=n_0+2, and

    e(k-2)=e(k-1)=1, e(k)=0.

Then k+3 is launched, unless a semantic halt occurs earlier.

If k is launched, its preceding launched candidate is k-1 or k-2, both with ending bit 1. Hence the next candidate is k+2; after that the ending bit of k forces the step to k+3. If k is skipped, k-1 is launched, and the next candidate is k+1 because steps never exceed 2. The ending bit of k-1 then forces the next step from k+1 to k+3. This covers every phase entering the interval.

## Shift encoding and local identities

Put `F(x)=P(0,1+x)`. For every x>=0 it encodes S followed by the raw continuation x. In particular `e(F(x))=e(x)`.

The elementary identities are

    F(x)+1=P(x+2,0),
    F(x)-1=P(1,x).

The first has an AX tag and zero continuation, so `e(F(x)+1)=1`.

For x>0, direct decoding gives

    e(F^4(x)-1)=e(F^2(x)+1)=1,
    e(F^4(x)-2)=e(F(x)+1)=1,
    e(F^4(x))=e(x).

For the first equality, F^4(x)-1 has MP tag and residual F^2(x)+1. For the second, F^4(x)-2 has AX tag: its first right projection is F^3(x)-1=P(1,F^2(x)), then the two extra fields leave residual F(x)+1.

More generally, for z>2 and j in {3,4,5}, three successive right projections of F^3(z)-j leave z+3-j. The outer tag is j>=2, so

    e(F^3(z)-j)=e(z+3-j).

All these residuals are positive. Applying this with z=F^4(x) gives

    e(F^7(x)-5)=1,
    e(F^7(x)-4)=1,
    e(F^7(x)-3)=e(x).

Consequently, if e(x)=0, the raw code q=F^7(x) satisfies the forced-hit criterion and is launched whenever it lies sufficiently far above the startup cutoff. Its actual command prefix is seven S commands followed by W(x).

## Cofinal reset prefixes

For arbitrary c,u,v>=0 define an AX wrapper

    A_(c,u,v)(q)=P(c+2,P(v,P(u,q))).

It executes AX(c;u,v), then raw continuation q. If q>5, then for j=3,4,5 the three right projections of `A(q)-j` leave `q-j`, while the outer selector stays >=2. Hence

    e(A(q)-j)=e(q-j).

This preserves the forced-hit pattern. Varying v makes these codes unbounded because P dominates its arguments. Therefore every x>0 with e(x)=0 gives a cofinal family of guaranteed-launched candidates

    P(c+2,P(v,P(u,F^7(x)))).

The wrapper resets additive counter and cache. The seven shifts may alter top, stack and cache or cause an earlier halt. This does not obstruct completeness when W(x) starts with a further AX reset and then applies a strong refutation block universal in the resulting top and stack.

## Strong compiler and the zero-continuation exception

The inherited three-command compiler supplies a word B_1;H that halts from every `(top,stack,0,0)` if the numerical calculus has a refutation. Prefix another AX command to reset counter and cache. Append three S commands after this halting word; these are never reached on a successful execution but fix the syntactic ending bit at zero.

Encode a nonempty command list backwards. A final command has residual zero. If the following raw-code suffix is r, set the current residual to `r+1-b`, then right-nest the current command fields around that residual. An intermediate suffix r=0 after MP or AX would incorrectly terminate. The appended terminal S^3 avoids this exception: the only zero raw suffix is the last S, whose predecessor is also S and thus uses residual 1; all earlier suffixes are positive. Every commanded continuation is therefore executed exactly.

The resulting x is positive, e(x)=0, and W(x) halts from every natural work tuple. The cofinal family above consists of successful, necessarily-launched candidates. Thus, from every finite cutoff and either initial bias, a native refutation forces this scheduler to halt.

This closes cofinality and strong-completeness for the scratch-biased enumerator. Soundness still requires a protected-tail or ordinary theorem-stack invariant at the actual initialized frame. The whole-tape runtime and exact blank startup are separate physical premises.
