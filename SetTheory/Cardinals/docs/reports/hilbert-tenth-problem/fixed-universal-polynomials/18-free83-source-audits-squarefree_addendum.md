# Independent addendum: even-parameter divisors and the squarefree slice

**PASS, separately from the already frozen auxiliary-square audit.** The two additional notes correctly prove:

1. If A>=2 is even, Delta=A^2-1, and a nonzero represented norm N=x^2-Delta*y^2 divides Delta, then N is a positive square or N<0 with Delta/|N| a square
2. On a genuine fixed-compiler slice of the exact83 source with squarefree Delta, every full positive zero satisfies norm_main=norm_input=norm_aux=1

The first statement classifies possible values; it does not assert that every value of these forms is represented. The second still does not normalize every factor or prove ordinary-input soundness.

## Source and scope

The independently authenticated scout is the same immutable commit `0d9d1e0174df30d82d80d758e9ba8e793203126e`, with JSON SHA-256 `682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016`. Its exact bytes and fetch metadata are copied to this addendum's `source/` directory. The upstream Python and saved arithmetic schedule remain unexecuted.

The prior core audit is preserved unchanged at `../free83-auxiliary-square-audit-20261003/AUDIT.md`. This addendum uses its proved positive-square auxiliary factor and its conditional retained-unit packing bounds. It does not extend that core verdict retroactively.

Both submitted addendum notes and the earlier f=1-only version are preserved in `source/`. The genuine compiler definitions d=bL, B=2^d, and input index I=2dx+b are visible in the preserved `FIXED_RAW_UNIVERSAL_76_PROOF.md`, Sections 1–2. The half-binomial compiler retains b,L,d and changes the masks as specified in its Section 1. Thus 1<=b<=d, B>=16, `twice_cell_bits=2d`, and `inner_bits=b`. These are inherited fixed-program hypotheses, not conclusions obtained by retyping a candidate's q.

Twenty-one additional literal source rows verify the actual loader, transport C, strong equation, and auxiliary V expression. In particular kappa=I+delta*Delta with positive delta, while the input norm's first coordinate mu may be signed.

## 1. Even-A represented-divisor classification

Write Delta=d*m^2 with d squarefree. Since A is even, Delta=3 modulo 4; hence d,m are odd and d=3 modulo 4. Write |N|=r*z^2 with r squarefree. N divides both Delta and x^2, so z divides m and x. With X=x/z and Y=my/z,

\[
 X^2-dY^2=\epsilon r,\quad \epsilon=\operatorname{sign}(N).
\]

Every prime dividing r divides X. If it did not divide d, it would also divide Y and then its square would divide the right side, impossible. Therefore r divides d as well as X. The integers

\[
 U=(X^2+dY^2)/r,\qquad W=2XY/r
\]

satisfy U^2-dW^2=1. We may replace x,y by absolute values. Then U>=1,W>=0. Since X and Y have opposite parity and r is odd, U is odd.

Let alpha+beta*sqrt(d) be the fundamental positive integer norm-one Pell unit. Such integer solutions form its nonnegative powers: multiplication by an inverse power reduces any positive solution to the interval from 1 to the fundamental unit, where minimality leaves only 1. The existing solution A+m*sqrt(d) has even first coordinate. If alpha were odd, d=3 modulo 4 would force beta even, and every power would have odd first coordinate. Thus alpha is even and beta odd. First-coordinate parity now alternates with the exponent, so the odd U belongs to an even power, say the 2h-th.

Pell duplication gives (U+1)/2=chi_alpha(h)^2. If epsilon=+1, this equals X^2/r, forcing squarefree r=1. If epsilon=-1, it equals dY^2/r, forcing squarefree d/r=1. Thus respectively

\[
 N=z^2\quad\text{or}\quad N=-d z^2,\qquad
 \Delta/|N|=(m/z)^2.
\]

The argument includes U=1,h=0. Directly, y=0 gives a positive square and x=0 forces y^2=1, N=-Delta. No zero-coordinate hole remains.

The even-A assumption is essential for this argument. At A=3, Delta=8, x=2,y=1 gives N=-4 dividing Delta, while Delta/|N|=2 is not square.

## 2. Exactly when the retained-unit bounds become available

Squarefree Delta forces A even: odd A would give 8 dividing A^2-1. The preceding classification and the core theorem therefore give

\[
 N_{main},N_{input}\in\{1,-\Delta\},\quad
 N_{strong}\in\{-1,\Delta\},\quad N_{aux}=1.
\]

Assume either main or input is -Delta. Since all seven nonzero integer factors have product Delta, two factors of absolute value Delta cannot occur. Hence the other Pell factor is +1, strong=-1, and the first/index/transport factors are units. The first unit is +1 by the already checked negative-unit descent. The product then forces the index and transport signs to agree, but either sign is allowed.

Only within this branch may one invoke transport unit magnitude to obtain C>=0. The exact shifted mask bounds from the core audit then give

\[
 1<R<a<\Delta,\qquad R+2<E.
\]

No claim here applies those bounds to an unnormalized general strong=-1 branch. No assumption that A, q, or a main rank had an earlier parity classification is inserted.

## 3. The input factor cannot be -Delta

If mu^2-Delta*kappa^2=-Delta, squarefreeness gives Delta dividing mu. Writing mu=Delta*b0, with b0 of either sign, yields

\[
 \kappa^2-\Delta b_0^2=1.
\]

Because kappa>0, kappa=chi_A(t) for t>=0. Modulo Delta this is A^t, hence 1 or A since A^2=1 modulo Delta.

The actual source instead gives kappa=I+delta*Delta, I=2dx+b. In this branch C=q-F-Z-alpha-2dx>=0, so 2dx<q. Also q=(B-1)J+1>=B=2^d>d and 1<=b<=d. Therefore

\[
 1<I<q+d<2q<A<\Delta.
\]

Here A=Y(X+1)+2 with X=wq,Y=sq^3 makes 2q<A immediate. Thus the residue I can be neither 1 nor A. This excludes the input -Delta branch without requiring mu>0 or t>0.

## 4. The Pell first-coordinate divisibility lemma is valid

For A>=2,m>=3, put f=psi_A(m) and D=chi_A(m). If

\[
 f\mid\chi_A(p)+\epsilon,\qquad\epsilon\in\{-1,1\},
\]

then 2m divides p and chi_A(p)=1 modulo f.

Indeed write p=qm+j with 0<=j<m. Since D^2=1 modulo f, addition identities reduce chi_A(p) to chi_A(j) if q is even, and to chi_A(m-j) if q is odd. For 1<=j<m, all chi_A(j) lie strictly between 1 and f-1, using

\[
 f-\chi_A(m-1)=A\psi_A(m-1)>1.
\]

The q-odd,j=0 endpoint is important: chi_A(m)=A f-psi_A(m-1) has residue f-psi_A(m-1), also strictly between 1 and f-1 when m>=3. It cannot produce either signed unit. Only q even,j=0 produces +1. The proof works over the composite residue ring and makes no illicit field cancellation.

For m=2, f=2A, and the weaker conclusion needed below is that p is even. Odd p gives chi_A(p)=0 modulo A and cannot be congruent to either signed unit modulo 2A.

## 5. The small-target odd-quotient obstruction is valid

For S>=2,k>=6,c=chi_S(k), and 1<L<S^2-1, no odd positive t and either sign satisfy

\[
 \epsilon\,\chi_S(t)/S\equiv-L\pmod c.
\]

The quotient is integral because t is odd. Pell duplication gives the pair at 2k congruent to (-1,0) modulo c. Reducing modulo 2k and reflecting about k thus makes chi_S(t) congruent to a signed chi_S(j), with odd 1<=j<=k.

If k is even, gcd(S,c)=1. Division yields quotient representatives ±chi_S(j)/S modulo c for odd j<k, each of magnitude less than c/2.

If k is odd, S divides c. One first uses the weaker numerator congruence modulo c, then divides it by S modulo c/S. The j=k representative becomes zero; the other magnitudes are less than (c/S)/2. This reduction deliberately weakens the original congruence and does not cancel a nonunit modulo c.

In both cases the smallest nonzero magnitude is 1. The next is

\[
 \chi_S(3)/S=4(S^2-1)+1>L.
\]

Finally c>S(S^2-1)^2>2SL. To verify the stated size bound explicitly, chi_S(6)>psi_S(6)>S(S^2-1)^2 by the sixth-rank identity from the core audit, and k>=6. Thus L lies below half of either relevant modulus; it cannot wrap to another representative. L>1 excludes the sole small magnitude.

## 6. The main factor cannot be -Delta, including all f

If main=-Delta, its actual positive root Dmain satisfies Delta dividing Dmain. Consequently

\[
 c=\chi_A(p),\quad Dmain=\Delta\psi_A(p),\quad p\ge1.
\]

In the retained-unit branch, the first norm and index still give k_first=2psi_P(n), n>=24, P>A. As c>k_first*Y>psi_A(n) and chi_A(n-1)<psi_A(n), one obtains p>=n>=24. This is weaker than the main-positive-rank relation in the core proof but sufficient.

Strong=-1 gives

\[
 S=\chi_A(m),\qquad f=\psi_A(m),\quad m\ge1.
\]

Auxiliary=1 gives V=epsilon*chi_S(t)/S for odd positive t, with epsilon the actual sign of V. For t=2h+1 the quotient polynomial Q_h has Q_h(1)=1. Since S^2=1+Delta*f^2,

\[
 |V|\equiv1\pmod {f^2},\qquad V\equiv\epsilon\pmod f.
\]

The exact source has V=-c modulo f, so f divides c+epsilon.

If m>=3, Section 4 forces 2m dividing p and c=1 modulo f. Since p>0,

\[
 c\ge\chi_A(2m)=1+2\Delta f^2.
\]

Using only T>=1 and R<Delta, the literal source gives

\[
 V=c(Tf-1)-Rf^2>c(f-1)-c/2>0.
\]

Thus epsilon=+1. It would require c=-1 modulo f as well as c=1 modulo f, impossible because f=psi_A(m)>2. Positivity of V is proved before selecting its sign.

If m=2, Section 4 forces even p=2k with k>=12. Then S=chi_A(2) and c=chi_S(k) by composition. If m=1, S=A,f=1 and c=chi_S(k) with k=p>=24. In either case put L=Rf^2. The retained-unit bounds give

\[
 1<L<\Delta f^2=S^2-1.
\]

The original source congruence V=-Rf^2 modulo c is exactly the obstruction in Section 5. Both signs of V remain covered. Thus neither m=1 nor m=2 is an omitted exception.

## 7. Final scope and remaining branches

The input and main -Delta branches are excluded. Every full positive83 zero on a squarefree-Delta genuine slice therefore has

\[
 N_{main}=N_{input}=N_{aux}=1.
\]

Two possibilities remain:

- Strong=Delta: first/index/transport are units, the first is +1, and index/transport have the same sign
- Strong=-1: first*index*transport=-Delta, with its remaining divisor and sign branches unresolved here

Neither case is automatically a full parent84 or parent85 zero. This addendum does not prove p=R, integrality of the deleted coefficient, an ordinary-input counterexample, or an 83-operation universal bound. It says nothing comparable about main/input normalization when Delta is not squarefree.

## 8. Independent probes

The new checker reads source rows only as inert JSON and uses its own elementary arithmetic. No upstream code or saved schedule is run. `CHECKS.json` records:

- 2,214,212 signed divisor-norm candidates for even A=2..200 and y=0..1000, with no separate x cutoff; all 645 represented solutions obey the classification, including 242 zero-coordinate cases
- 439,432 signed first-coordinate divisibility tests for A=2..60,m=3..30,p=0..8m; all 8,260 hits satisfy the claimed conclusion; the m=2 parity boundary is checked separately
- 975 complete odd-quotient recurrence cycles modulo chi_S(k), S=2..40,k=6..30: 257,580 states cover both signs and every integer target 1<L<S^2-1
- 17,400 auxiliary quotient residues, 6,032 m>=3 positive-V contradictions, and 1,102 m=1,2 composition checks
- 6,464 squarefree input residues and 34 independent loader-size cases

These checks support the unbounded proofs; they do not materialize complete compiler zeros. Replay from any directory with `python3 audit_addendum.py`; explicit exceptions keep all checks active under `python3 -O` too.
