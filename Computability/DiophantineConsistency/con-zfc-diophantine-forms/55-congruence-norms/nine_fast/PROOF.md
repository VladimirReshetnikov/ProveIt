# Congruence separation: the 604-operation nine-positive-variable equation

This component is the short arithmetic variant of the new congruence-separated
nine-variable construction. Its primary polynomial has exact total degree
**6,692,108**, with **604 live binary arithmetic operations** for nine positive
integer variables, or **610 operations** for its nine-natural-variable
translate. Its certificate circuit is a different expression for the **same
polynomial**, with multiplier 1.

The native coefficient tuple and the original 31-positive-variable source
remain unchanged. The common source frontend evaluates the unshifted
94-record system at the packed word `1+g+ell`. Its authoritative targets are
`upstream/code_positive.json`; original rows 13 and 21 use targets 2124 and
1059, respectively. The separate finite source audit checks all 49,632
record-by-word interactions. The previous shifted targets are invalid for
these unshifted records.

## Source positivity and the even-coordinate restriction

The source coefficient polynomial has leading coefficient 1, degree 5102 in
the base, and at most 94 coefficient records, each of magnitude less than
`2^2134926`. The base is at least `4*2^2134940`. Its positive leading monomial
therefore dominates every possible negative lower contribution. The source
mask is positive by comparison with the complete geometric sum. Thus the
calibrated source register `R` and threshold `N` are at least 8 on every
allowed input, and the positive Jones ratio-register hypotheses are valid.

Replace the packed coordinate and Jones multiplier by `g=2g'`, `h=2h'`, with
`g',h'>0`. The base, block length, and block modulus are even; therefore the
source register `S=g+N0*Jcode` is even and

\[
R=L^2+(S+T)L+L-1-S
\]

is odd. Jones's `P=2M^2U` is even, so `K=R+1+h(P-1)` is even. Hence

\[
a_0=(P^2-1)K^2+1\equiv1\pmod4.
\]

Completeness of these restrictions is constructive. For a positive source
zero, write its coordinates as `n_i+1`. The canonical word
`g=sum n_i*base^w_i` is even because all weights are positive. It is nonzero:
the all-one positive tuple fails parent residual 5, `E X+E-a X=0`, with value
1. Thus `g/2>0`. The inherited construction `exists_B25core` in
`upstream/Ratio.lean` explicitly chooses `K=psi_P(R+1)`, where
`psi_P(0)=0`, `psi_P(1)=1`, and
`psi_P(n+2)=2P*psi_P(n+1)-psi_P(n)`. This recurrence gives
`psi_P(n)=n (mod2)`. Therefore `K` is even; the defining congruence with odd
`P-1` then makes its positive witness `h` even. No unproved assumption about
cofinality in a congruence class is used.

## A simple strict polynomial majorant

Retain the Jones registers `A,C,D,E,F,G,H,I,J,i`, and set

\[
e=iJC,\quad D=(A^2-1)C^2+1,\quad F=e^2D^2(D-1)+1,
\quad I=(G^2-1)H^2+1.
\]

Define

\[
S_0=e(8D^2-4D-1),\qquad V_0=PK,\qquad V_1=S_0GH,
\qquad a_1=64DFI.
\]

The exact identity

\[
S_0^2-64DF=e^2(8D+1)-64D=:\varepsilon
\]

is verified by expansion. Since `A>=3`, `J=4A-5>=7`, and `i,C>=1`, we have
`e>=7`, so `epsilon>0`. Also `S0>0`, `G,H>0` and `I<=G^2H^2`. Therefore
`V1>sqrt(a1)`. We have `V0^2-a0=K^2-1>0`, so `V0>sqrt(a0)` as well.
These inequalities hold for all allowed inputs.

Let

\[
\delta_0=K^2-1,\qquad
\delta_1=\varepsilon G^2H^2+64DF(H^2-1).
\]

Direct substitution into `I=(G^2-1)H^2+1` proves

\[
\delta_1=V_1^2-64DFI=V_1^2-a_1.
\]

## The two-root norm and the ratio conditions

Write

\[
u=JF>0,\quad v=QF+J(H-C)>0,\quad M_d=Q+H-C,
\quad\Omega=u(2\mu-1),\quad E_0=un+v-\Omega M_d,
\]

where `mu` is the unchanged Jones margin. The inherited positive-register
bounds give `0<v/u<=Md`. Put

\[
\Theta=E_0-\Omega(V_0+V_1),\qquad
F_9=(\Theta^2-\Omega^2(a_0+a_1))^2-4\Omega^4a_0a_1.
\]

Because `mu` is integral and `u>0`, `Omega!=0`. The radicands are positive,
and `a0=1 (mod4)` while `a1=0 (mod4)`, so they are unequal. If `F9=0`,
set `t=Theta/Omega`. The identity `(t^2-a0-a1)^2=4a0a1` first gives `t!=0`,
then the rational numbers

\[
r_0=(t^2+a_0-a_1)/(2t),\qquad r_1=t-r_0
\]

satisfy `r0^2=a0`, `r1^2=a1`. Rational square roots of integers are integers.
Thus `a0` and `DFI` are squares and `t=r0+r1` is integral. The strict integer
majorants imply `|rj|<=Vj-1`, so

\[
Z=M_d+V_0+V_1+r_0+r_1\ge M_d+2>0.
\]

The vanishing factor gives `n+v/u=(2mu-1)Z`. Its left side is positive, hence
`mu>0`, and its right side is integral, hence `u|v`. These are precisely the
unchanged four Jones ratio conditions.

Conversely, given the four conditions, choose integer roots `r0,r1`, form
`Z` as above, and choose `n=(2mu-1)Z-v/u`. This is an integer at least 2,
so an allowed natural coordinate. Its selected norm factor vanishes. Combined
with the even-coordinate completeness, this preserves source solvability in
both directions.

## Exact degree and reproducibility

The certificate replaces the inner expression by the polynomial identity

\[
\Theta^2-\Omega^2(a_0+a_1)
=E_0^2-2E_0\Omega(V_0+V_1)
+\Omega^2(\delta_0+\delta_1+2V_0V_1).
\]

This exposes the cancellation that a degree walk on the primary circuit
would miss. Its decisive exact degrees are

\[
\deg\Omega=791147,\quad\deg\delta_1=1763760,
\quad\deg(\text{inner})=3346054,
\quad\deg F_9=6692108.
\]

The degree of the other norm summand is strictly smaller. The diagonal top
coefficient is

\[
2^{566}\,\alpha^{3345748}\,\gamma^{400},\qquad
\alpha=2^{2134940},\quad\gamma=2^{16012040},
\]

which is nonzero. `check_circuits.py` independently checks the basic `S0`
identity coefficientwise, then propagates syntactic degree bounds and diagonal
leading coefficients modulo three primes using the actual fixed payloads.
Its nonzero output coefficients prove the total-degree upper bound is attained.
It also checks 240 actual-coefficient modular equalities between primary and
certificate expressions, 40 parity fixtures, gate liveness, and operation
counts. The implementation checks supplement the universal proof above.

Run `python3 build_nine.py` followed by `python3 check_circuits.py`.
The common source theorem, native unbounded compiler, coefficient calibration,
and Jones ratio arithmetic remain expressly inherited dependencies. The result
is an ordinary theorem formalizable in ZFC; the release does not claim an
exported proof-assistant derivation of the full literal polynomial endpoint.
