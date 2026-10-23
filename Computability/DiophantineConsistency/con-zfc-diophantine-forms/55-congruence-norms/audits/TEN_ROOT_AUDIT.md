# Independent audit: the two-root ten-integer finalizer

Date: 2026-10-23. Repository intake pin:
`4b4349064a750ba6347293b55874a7f92abdd0db`.

## Verdict and scope

The new congruence restrictions and two-root finalizer are sound, and their
completeness follows from the *actual constructive witnesses* in Sun's Lucas
bridge. No new unproved congruence-cofinality assertion is needed. The signed
cases, zero cases, rational-root cancellation, and recovery of the removed
factor `old_f^2*l^2` are addressed below.

The audited construction is `ten/build.py`, using the
**corrected unshifted source code** `code_positive.json`. The old shifted code
must not be substituted: two coefficients that had canceled after shifting
reappear in the unshifted source. The corrected target for original row 13 is
2124, and for row 21 is 1059. The root's finite source audit verifies all
49,632 record-by-word interactions. The ten-variable congruences below depend
only on the number of targets (22), their positive integral exponents, and the
common base; they are unaffected by this correction.

The final corrected circuit folds the unused intermediate old-f expression
into b=6f+4 and has **586 arithmetic operations** and exact degree
**9,152,284**. I independently replayed the component verifier: its top-degree
coefficients modulo 1000003, 1000033, and 1000037 are 474647, 56488, and
452960, respectively. These nonzero residues establish that its syntactic
upper bound is attained. Its generated circuit SHA256 and further independent
checks are recorded in `TEN_ROOT_CHECKS.json`.

The source compiler, fixed coefficient calibration, and native unbounded
machine interpretation remain inherited ordinary mathematics. This is not an
exported internal ZFC derivation or a new proof-assistant formalization of the
whole literal circuit. The new arithmetic reduction is a universal ordinary
proof and is not inferred from finite tests.

## 1. Notation and exact universal congruences

The free variables are ten arbitrary integers `f,g,h,k,l,w,x,y,z,m`. Distinguish
the free variables from the following substituted bridge variables:

\[
 f_0=2f+1,\quad b=1+3f_0=6f+4,\quad
 g_0=bg,\quad h_0=bh,\quad k_0=b(3k+2).
\]

Thus `b` is even, `b=1 (mod 3)`, nonzero, and `|b|>=2`. Set
`base=2^2134940*b^2`. All source weights are positive. With the source compiler's
registers,

\[
\begin{split}
M_c&=N_0-1-(b-1)\ell,\\
T_c&=M_c+(\mathrm{base}-2)\mathrm{target}\,N_0,\\
S_c&=g_0+N_0J_c,\\
X&=N^2+(S_c+T_c)N+N-1-S_c.
\end{split}
\]

Here `N0,N` are positive powers/products of `base`, and `target` has exactly
22 terms, each a power of `base`. Consequently,

\[
\mathrm{base}\equiv N_0\equiv N\equiv1\pmod3,
\quad M_c\equiv0,\quad T_c\equiv-22\equiv2\pmod3,
\quad X\equiv1+T_c\equiv0\pmod3.
\]

Also `N0,N` are even and divisible by `b^2`; `g0` and `Sc` are even. Therefore
`X` is odd and `b | X+1`. These facts hold for every integer assignment,
without an assumption that the final polynomial vanishes.

The source's `Y` is an integer multiple of `2b`. For the standard Sun bridge
registers

\[
\begin{gathered}
L=lY,\quad U=2LX,\quad V=4g_0wY,\quad A=U(V+1),\quad
B=2X+1,\quad C=B+(A-2)h_0,\\
P=U^2V,\quad P_{1/2}=P/2= (LX)UV,\quad
K=X+1+k_0(P-2),\quad Q=(P_{1/2}^2-1)K^2+1,
\end{gathered}
\]

the expression for `P_half` is division-free. We have

\[
4b\mid A,\quad 2\mid P_{1/2},\quad 3\mid P,
\quad b\mid K,\quad3\mid K,
\quad Q\equiv1\pmod{b^2},\quad Q\equiv1\pmod3.
\]

For `3|K`, use `X=0 (mod3)`, `k0=2 (mod3)`, and `P-2=1 (mod3)`.
In particular `Q` is odd, nonzero, and `gcd(b,Q)=1`. Finally,

\[
C\equiv-1\pmod b,\qquad
D=(A^2-4)C^2+4=A^2C^2-4(C^2-1)\equiv0\pmod{4b}.
\]

Let `Delta` be the inherited signed margin

\[
\Delta=8\mathscr C^3g_0K^2-
g_0^2\bigl(32(C-KL)^2\mathscr C^3+g_0^2K^2\bigr),
\qquad\mathscr C=b\,\mathrm{base}^{W}.
\]

Put

\[
r=bQ,\qquad a=r+(3\Delta-1)(rz)^2,
\qquad d=DFI^*.
\]

Since `b` is even and `Q` is odd,

\[
\frac ab=Q+(3\Delta-1)bQ^2z^2\equiv1\pmod2,
\qquad \frac db\equiv0\pmod2.
\]

Both quotients are integers, including when `b<0`. Thus **`a != d` on every
integer assignment**. Also `r=1 (mod3)` and `|r|>=2`.

## 2. Exact two-root extraction without sign assumptions

For integers `a,d` with `a!=d`, suppose a rational number `t` satisfies

\[
(t^2-a-d)^2-4ad=0.
\]

If `t=0` the equation is `(a-d)^2=0`, a contradiction. Define

\[
u=\frac{t^2+a-d}{2t},\qquad v=t-u.
\]

Expanding the displayed equation gives `u^2=a` and `v^2=d`. Hence each of
`a,d` is a nonnegative rational square, and therefore an integer square.
Moreover `u,v` are integers, so `t=u+v` is an integer. No positivity premise
for the radicands and no field-independence premise is required.

This is the precise reason universal *inequality of the two radicands* is
enough. Mere inequality would not suffice for three or more radical terms,
but there are exactly two terms here.

## 3. The shared square/positivity guard

Suppose `z!=0` and `a` is an integer square. Factor

\[
a=r\,H,\qquad H=1+(3\Delta-1)rz^2.
\]

We have `gcd(r,H)=1`. Neither factor vanishes: `r!=0`, and `H=0` would force
`r | 1`, contrary to `|r|>=2`. Since their product is a nonzero square, each
factor is a square or the negative of a square, with the same sign. But
`r=1 (mod3)`, whereas a negative square is 0 or 2 modulo 3. Hence `r` and `H`
are positive squares.

Now `r=bQ` and `gcd(b,Q)=1`. The same signed coprime-factor argument, using
`b=Q=1 (mod3)`, proves that **`b` and `Q` are positive squares**. As `b` is
even, `b>=4`, and therefore `r>=4`.

If `Delta<=0`, then `3Delta-1<=-1` and

\[
H\le1-rz^2\le-3,
\]

contrary to its positivity. Thus **`Delta>0`**.

Conversely, suppose `b,Q` are positive squares and `Delta>0`. Then `r=bQ` is
a positive square, while `3Delta-1` is positive and equals 2 modulo 3, hence
is not a square. The positive integer `(3Delta-1)r` is consequently nonsquare.
The ordinary Pell theorem supplies integers `q,z` with `z>0` satisfying

\[
q^2-(3\Delta-1)r z^2=1.
\]

It follows that `a=rq^2` is a square. This Pell witness can be chosen before
the Lucas interpolation witnesses `xi,y`.

## 4. Recovery of the removed `f0^2*l^2` factor

From the guard, `b>0`, hence `Ccap>0`. If `g0<=0`, every term of `Delta` is
nonpositive, so `Delta>0` forces `g0>0`. If `K=0`,

\[
\Delta=-32g_0^2C^2\mathscr C^3\le0,
\]

also impossible. Thus `K!=0`.

If `l=0`, then `U=P=P_half=0` and `Q=1-K^2`. Since the guard forces `Q>0`,
integrality gives `K=0`, a contradiction. Therefore `l!=0`. Since `f0=2f+1`
is never zero, the old bridge hypothesis

\[
O_0=f_0^2l^2\Delta>0
\]

is recovered. Also `R2=4Q` is a square. Thus dropping the prefactor from the
new guard does not lose a hypothesis of the inherited reverse bridge.

## 5. Quintic divisibility and the final polynomial

The inherited quintic is

\[
\pi(t)=(t^3-t-1)(t^2+23).
\]

It has no rational root and has a root modulo every positive integer.
For completeness of the latter fact: at `p=23`, the cubic has the simple
root 3; at odd `p!=23`, either the cubic has a simple root, or its irreducible
cubic Frobenius permutation is a 3-cycle, so its discriminant `-23` is a
nonzero square and the quadratic factor has a simple root. Hensel lifting
handles all odd prime powers. At 2, `-23=1 (mod8)` is a 2-adic square. The
Chinese remainder theorem combines these local roots. The cubic's rational
root theorem and the sign of the quadratic prove absence of rational roots.

With `S=2A-5` (always a nonzero odd integer), `T=3b w C-2((bw)^2-1)`, and
`xi=zx`, define

\[
\begin{gathered}
R=T+Sy,\quad
\Theta=(R^3-RS^2-S^3)(R^2+23S^2),\quad\Sigma=\xi S^5.
\end{gathered}
\]

`Theta` never vanishes: its vanishing would make `R/S` a rational root of
`pi`. If `Sigma|Theta`, then `S|T`. Indeed, if `v_p(T)<v_p(S)`, then
`v_p(R)=v_p(T)=beta<alpha=v_p(S)`. The two factors of `Theta` have valuations
exactly `3beta` and `2beta`, so `v_p(Theta)=5beta<5alpha`, contradicting
`S^5|Theta`.

The final polynomial is

\[
\mathcal F=
\bigl((\Sigma m-\Theta)^2-\Sigma^2(a+d)\bigr)^2
-4\Sigma^4ad.
\]

If `F=0` and `Sigma=0`, this reads `Theta^4=0`, impossible. Thus `Sigma!=0`,
in particular `xi!=0` and `z!=0`. Divide by `Sigma^4` and apply Section 2 with
`t=m-Theta/Sigma`. We obtain that `a,d` are integer squares and `t` is an
integer. Hence `Sigma|Theta`, so `S|T`. Sections 3 and 4 recover `b` square,
`R2` square, `O0>0`, and all nonzero hypotheses. The inherited Sun reverse
bridge now yields the source relation.

## 6. Completeness of the imposed residue classes

Start with a solution of the fixed positive parent source system. Its source
encoding is cofinal in sufficiently large powers of two. Choose

\[
b=4^s\quad(s\ge1),\qquad f=(b-4)/6\in\mathbb Z.
\]

Write the positive source coordinates as `n_i+1`, and take the canonical
packed word `g0=sum n_i*base^w_i`. Since every `w_i>0`, `b^2|g0`. The word
is nonzero: if all `n_i=0`, every parent coordinate would be 1, but parent
residual 5, `E X+E-a X`, then equals 1, independently of the fixed ports.
The inherited source size bound gives `b<=g0<Ccap` for sufficiently large
`b`. In this canonical construction `b^2|X+1`, because both `N,N0` and `g0`
are divisible by `b^2`.

The needed exact positive bridge choices are verified in the primary source:
[Sun, *Further results on Hilbert's Tenth Problem*, v7](https://arxiv.org/html/1704.03504v7),
Theorem 4.12, the paragraph following `u_B(A)=B (mod A-2)`, and equation
(4.16). After `P=2,Q=1` specialization they construct

\[
C=u_{2X+1}(A),\qquad K=u_{X+1}(U^2V),
\]

where `u_0(t)=0,u_1(t)=1,u_(n+2)(t)=t*u_(n+1)(t)-u_n(t)`.
These are constructive witnesses, not an assumed description of arbitrary
square certificates.

Since `X` is odd, `X+1` is even. Every even-index Lucas polynomial is
divisible by its parameter. Thus `P|K`, in particular `b^2|K` and `3|K`.
The integer

\[
k_0=\frac{K-X-1}{P-2}
\]

has numerator divisible by `b^2`. Since `4|P`, the denominator has exactly
one factor of 2; because `b` is a power of 2 and `b>=4`, this implies
`b|k0`. Reduction modulo 3 gives `k0=2 (mod3)`. As `b=1 (mod3)`,
`k0/b=2 (mod3)`, so `k0=b(3k+2)` for an integer free coordinate `k`.

For the other restriction, the odd-index Lucas polynomial satisfies

\[
u_{2X+1}(A)\equiv(-1)^X=-1\pmod{A^2}.
\]

Since `4b|A`, we have `2b^2|C+1`. Also `B+1=2(X+1)` is divisible by
`2b^2`. Therefore `2b^2|C-B`. The denominator `A-2` has exactly one factor
of 2, and

\[
h_0=\frac{C-B}{A-2}
\]

is an integer divisible by `b^2`, hence by `b`. The source restriction
`g0=bg` is automatic as well. The new residue classes consequently retain
the canonical positive bridge completion.

This completion supplies `Delta>0`, `S|T`, and a square `R2=4Q`; hence `Q`
is a positive square. Section 3 chooses a positive Pell witness `z` making
`a` square. Theorem 4.1 in
[Sun, *Ten unknowns for Hilbert's tenth problem over the integers*, v1](https://arxiv.org/html/2609.01594v1)
then chooses a positive `xi` divisible by `z`, and permits the second Lucas
witness `y` to be prescribed modulo `xi` while making `d=DFI*` square.
Put `x=xi/z`. Write `T/S=q`, choose a root `c` of `pi` modulo `xi`, and
request `y=c-q (mod xi)`. This yields `Sigma|Theta`.

Both roots of `a,d` are integral. Select an integer `m` satisfying
`m-Theta/Sigma=sqrt(a)+sqrt(d)`; then the displayed quartic vanishes. This
proves completeness without adding variables.

## 7. Finite independent checks

Run `python3 audits/ten_root_audit.py`. The checker reads the actual
fixed coefficient bytes and reports:

* 128 generated-DAG congruence cases, including negative base, zero witnesses,
  and all new universal residue invariants;
* 413,820 rational-center norm inputs, with all 100 zeros satisfying the
  integer-square extraction conclusion;
* 12,936 signed guard inputs, with all 24 square outcomes satisfying positive
  square base, positive square `Q`, and positive `Delta`;
* 54 constructive Lucas cases, with exact modular checks of the quotient
  conditions `b|h0` and `k0/b=2 (mod3)`.

The checker passed. These are regression and implementation checks. The
unbounded proof is Sections 1--6, together with the expressly inherited
source/compiler and Lucas theorems.
