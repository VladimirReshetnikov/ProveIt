# One linear residual for a fixed input boundary

## Result and limitations

This note supplies a previously missing *interface theorem*, not a new measured
Con(ZFC) endpoint. A fixed finite input can be inserted into the native periodic
Wang compiler with one linear residual, or by an affine coordinate replacement with **no
additional variables or residuals** in the existing lifted sources. The tile alphabet need not contain one state/tile per input symbol,
and polynomial degree need not depend on input length. The price is coefficient
bitlength linear in that length. An explicit small universal machine together
with its compiled ZFC-refuter input has **not** been supplied here.

## Native hypotheses

Use a finite directed-signal Wang language and the native compiler interface:
B=2^d is fixed; a solution recovers C=sum_{i=0}^{N-1} c_i B^i with 0<=c_i<B;
the marked tile is cell 0; positive i moves one cell to the left; each admissible
tile t has a fixed native digit enc(t), with all dummy digits zero. Canonical
accepting witnesses permit arbitrary sufficiently large independent spatial
width and temporal height. The rank controller may alter free dummy digits
away from a fixed finite set of cells. All four ports must be regenerated
for the new language and remain bound as one tuple.

Let t_0,...,t_{m-1} be a fixed consecutive initializer block, in right-to-left
order, starting at the distinguished marker. Put

D=sum_{i=0}^{m-1} enc(t_i) B^i, M=B^m.

Assume enc(t_{m-1})>0. Add V in Z and the residual

                 C - D - M V = 0.                         (B)

Since 0<=D<M and C>=0, (B) implies V>=0. Uniqueness of radix-B expansion
forces precisely those first m digits. It also forces N>=m because
D>=B^(m-1) and C<B^N. Conversely any native word with that prefix satisfies
(B), with V=floor(C/M). Dummy digits in the prefix are fixed to zero. No
separate positivity guard, inequality, or variable exponent is introduced.

If the underlying system has residual degrees at most 2 and C is affine in
its coordinates, appending (B) preserves degree 2 for the system and degree
4 for its sum of squares. In the existing lifted source C=(beta J+1)-F-alpha
is affine, so this hypothesis holds literally. The operation M=B^m is a
fixed coefficient definition, not exponentiation of an unknown. Its exact binary bitlength is floor(m log2 B)+1; since the native B is a power of two, this equals m log2 B+1 here.

## Zero-cost affine absorption

When C=q-F-alpha and alpha is an independent unrestricted coordinate, replace
alpha everywhere in the original system by q-F-D-M V. Keep V as the replacement
coordinate, and do not append (B). Then C is identically D+M V. The new system
has exactly the old number of variables and residuals, and degree cannot
increase under affine substitution. Its solutions are in bijection with old
solutions satisfying the boundary congruence: forward map uses the displayed
alpha, and inverse map uses V=(C-D)/M. This argument does not discard any old
positivity guard on alpha: every occurrence, including its guard, is substituted.
Thus the 42-integer quartic *architecture* accommodates a fixed universal input
with no variable-count or degree penalty, once its native tuple is regenerated.
This is not yet a new concrete 42-integer consistency polynomial.

For a strictly positive replacement coordinate one may instead use
C=D+M(V+1), losing the V=0 solutions. Completeness survives if canonical padded
witnesses contain an occupied cell past the fixed prefix. The unrestricted
integer variant needs no such additional convention.

## A constant-size initialization language

Fix a deterministic two-sided TM with alphabet Gamma (blank 0), start q0,
and absorbing halt state. For a nonempty input a0...a_(ell-1), add horizontal
phase colors L,D,R, reset HB, and ordinary O; add fresh vertical I,Q,H,V.
Initialization tiles (west,north,east,south) are:

- (L,I,L,0) and (R,I,R,0): blank margins;
- (L,I,D,head(q0,a)) for every a in Gamma: first input symbol;
- (D,I,D,a) for every a in Gamma: remaining input symbols;
- (D,Q,R,0): the distinguished right delimiter (Start).

Add reset tiles (HB,H,HB,I) and (HB,H,HB,Q); ordinary transition, receiving,
headless, halt, and finish tiles exactly as in the directed-signal compiler;
and nine seams with vertical V and horizontal pairs in
{O,HB,R} x {O,HB,L}. Forbid the standard impossible BAD-west tile.

The prescribed block is Start, then the ell-1 data tiles for
 a_(ell-1),...,a1, then the first-symbol tile for a0. Thus m=ell+1. If ell=1
there are no data tiles in the block. Empty input can instead be represented
by the single blank symbol a0=0.

Matching immediately to its left requires the L blank phase until a seam;
matching to its right requires the R blank phase until a seam. There is no
phase cycle crossing D->R or L->D. Periodicity therefore forces seams on both
sides, and the complete strip initializes exactly the chosen finite input,
with one head and blank margins. Reset/H and ordinary-step arguments are
unchanged from the native directed-signal proof. The first subsequent reset
row can occur only after a halt. Conversely a finite halting run has arbitrarily
large blank margins and absorbing halt padding, so produces the required
helical periodic tiling and prefix.

The new initializer has 2|Gamma|+3 tiles, independent of ell. For n working
states and s symbols, a generous bound on the whole language is
 n s + s(|SR|+|SL|) + 6s + 15,
where SR,SL include halt if targeted. Hence a total 5-state/5-symbol transition
machine with one extra halt state requires at most 130 tiles. This is only
a conditional tile-count bound, not a claim that a pinned 130-tile ZFC
instance or small universal-machine input has been constructed.

## The displaced rank controller

The existing controller has an odd prime lambda and chooses N=lambda^n cells, T=N/lambda,
C0=d lambda, k=lambda-1. Its number-theoretic hypotheses ensure the residues
{B^(kj):0<=j<T} are exactly {1+C0 z mod C0 T:0<=z<T}. Assume T>C0,
gcd(B,C0 T)=1, and lambda does not divide B-1. These are exactly the
properties used by the existing Boolean coverage argument.

Replace its mutable positions {2+kj} plus {3} by {a+kj} plus {a+1},
where a>=m is fixed. Every residue modulo dN still has a Boolean subset
representation. Divide the target by B^a. Choose epsilon in {0,1} so that
r B^(-a)-epsilon B is nonzero modulo lambda. Let b be its residue modulo
C0; then 1<=b<C0<T and gcd(b,T)=1. Write the remaining target as b+C0 u.
Choose z0 modulo T solving b z0+b(b-1)/2=u modulo T, and choose the b
orbit members with coordinates z0,...,z0+b-1 modulo T. Include the extra
cell a+1 iff epsilon=1. Their sum is the target. Since k>1, the extra cell
is not an orbit cell. This is exactly the original proof with the common
invertible factor translated, not a new unproved density assertion.

For fixed a,m and sufficiently large independent power-of-lambda width w
and height h, with N=wh, all mutable positions and their required translations
remain below N: their maximum is a+k(T-1), and the spare margin is
N-[a+k(T-1)]=T+k-a. Choose h large enough that w+1<T+k-a. The prefix
0,...,m-1 remains unchanged. Consequently the full canonical rank/parity/
odd-scale conclusions survive the boundary constraint whenever the regenerated
native tuple satisfies the original arithmetic-controller hypotheses.

## Exact logical scope

For any fixed machine U and explicit word w, the augmented native system has
a solution iff U halts on w, subject to the named native-interface hypotheses.
If ZFC proves Halt(U,w) iff not Con(ZFC), its lack of solutions is provably
equivalent in ZFC to Con(ZFC). This note proves the boundary adapter only.
To make a competitive final endpoint one must still materialize U,w, regenerate
its complete native tuple, verify its carry/rank-controller hypotheses, and
measure the resulting coefficient payload. Reusing the old K215 ports for the
new language would be invalid.
