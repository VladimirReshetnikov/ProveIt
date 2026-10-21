# Credit theorem for automatic MP followed by transfer

This theorem concerns the abstract three-command interpreter in
`research215_round4_calculus/AUTOMATIC_MP_COMPILER.md`. It is not a physical
machine calibration. Source allocation and blank initialization are separate.

Let P be Cantor pairing, f its right projection, and T_q=q(q+1)/2.
Commands have fields S=[0], M(x)=[1,x], AX(c;x,y)=[c+2,y,x]. At a positive
continuation cursor the ordinary scheduler decrements once before decoding.
Use conservative balances S=-1, M=-1, AX=10. The automatic M has no successful
zero push; its final transfer consumes one stack head in either nonhalting branch.

## A uniform counting bound

Let k(n) be the number of S and M commands in the complete syntactic word of
candidate n, ignoring halts. Set g(0)=0 and g(r)=k(r-1) for positive r, and
B(N)=sum_{n<N} k(n). Exact decoding gives

- k(P(0,y))=1+g(y),
- k(P(1,y))=1+g(f(y)),
- k(P(a,y))=g(f(f(y))) when a>=2.

Claim: B(N)<=2N for every natural N.

Use strong induction. N=0,1,2 are checked directly. A sequence u with u(0)=0
and prefix sums at most 2(L-1) for every positive relevant L has pullback
prefix sums through f at most 2(L-r(L)), where r(L) is the number of nonempty
Cantor diagonal blocks below L. Each full or partial diagonal enumerates a
prefix 0,...,j and loses at least two units against twice its length.
For g, the needed prefix sum is B(L-1)<=2(L-1). The same bound applies again
to g composed with f. Write H and H2 for the first and second pullback sums.

At a triangular boundary with q>=2,

 B(T_q)=q+B(q-1)+(q-1)+H(q-1)+sum_{l=1}^{q-2} H2(l)
       <=q^2+3q-3-2 sum_{l=1}^{q-1} r(l)
       <=q^2+q-1 < 2T_q.

All induction indices are smaller than T_q; q=1 is a direct base. At a partial
diagonal N=T_q+j, 0<=j<=q, the first q-1 entries are AX roots. For j<=q-1,
the extra cost is H2(j)<=2j. At j=q the added MP root gives total extra cost

 H2(q-1)+1+g(f(q-1)) <= 2(q-1-r(q-1))+1+2r(q-1)=2q-1.

Here g(m)=k(m-1)<=B(m)<=2m and f(q-1)<=r(q-1). Thus the partial diagonal also
obeys B(N)<=2N. This completes the induction.

## Credit for the actual consecutive schedule

Consider candidates 1,2,3,..., as in the intended source. Before candidate n,
there are n-1 earlier candidates. If q is the Cantor diagonal number of n,
at most 2q+1 of the indices through n have a non-AX root. Thus at least
n-2q-2 earlier selected candidates have already completed their first AX.
At any point within candidate n, all negative costs so far are bounded by
B(n+1)<=2(n+1), including those in unselected candidate zero. Ignoring all
other positive AX contributions gives the valid lower bound

 10(n-2q-2)-2(n+1) >= 8n-20 sqrt(2n)-22.

This is positive for n>=32 and increasing thereafter. The exact finite
words for candidates 1 through 31 therefore complete the infinite proof.
The owned checker `check_credit.py` expands these words directly, checks
all internal prefixes, and finds minimum -3, first attained at the end of
candidate 2: candidate 1 is M, and candidate 2 is S;S. Candidate 3 begins AX.
The checker also supplies a longer counting sanity check, not used as an
extrapolation for the infinite argument.

Consequently ten initial theorem heads above an arbitrary opaque stack tail
leave at least seven heads forever. S and M consume one head; AX pushes ten.
Arithmetic macro interiors have no additional logical halting sites. An M
success with consequent 1 halts soundly at its automatic transfer; otherwise
its output top/cache remain theorems, provided the consumed stack head is safe.
A blank-start implementation must independently establish the stated initial
wrapper and candidate cutoff before this theorem can be applied.
