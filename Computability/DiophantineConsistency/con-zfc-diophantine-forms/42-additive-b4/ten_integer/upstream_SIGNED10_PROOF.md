# A completely fixed equation in ten unrestricted integer variables

## 1. Result, scope, and attribution

The circuit `generated/signed10.json` defines one polynomial

\[
F_{10}(f,g,h,k,l,w,x,y,z,m)\in\mathbb Z[f,g,h,k,l,w,x,y,z,m]
\]

with **ten unrestricted integer unknowns**. Its coefficients are fixed by
`data/INSTANCE.json`; there is no existential coefficient, unspecified r.e.
index, variable exponent, division, radical, or auxiliary witness in this
polynomial. Its exact degree is

\[
126496\,5^{31}+27064.
\]

Together with the inherited machine/compiler endpoint, the quartic31
reduction, and this package's complete coefficient adapter, the construction
proves in ZFC that

\[
\exists(f,g,h,k,l,w,x,y,z,m)\in\mathbb Z^{10}\ F_{10}=0
\quad\Longleftrightarrow\quad\neg\operatorname{Con}(\mathrm{ZFC}).
\]

Consequently its lack of integer solutions is equivalent, in ZFC, to
`Con(ZFC)` for the repository's chosen proof predicate. This is an ordinary
mathematical proof assembled from explicit arithmetic identities and the
cited theorems, not an end-to-end machine-checked formal certificate.

The general reduction to ten integer variables is **Sun's 2026 theorem**,
not a new universal unknown-count theorem claimed here. The present work
specializes its previously published source-coding recipe to the literal
quartic31 Con(ZFC) instance, and then simplifies its final equation in three
ways: a quintic divisibility/nonvanishing merger, a coprime merger of two
square conditions, and smaller separating weights. The literal Sun variant
and intermediate variants are retained for comparison.

Primary sources:

* Zhi-Wei Sun, *Further results on Hilbert's Tenth Problem*, Sci. China Math.
  64 (2021), 281–306, arXiv:1704.03504v7, Theorem 3.1 and its explicit proof;
  Theorems 4.12–4.13; equations (5.1), (5.4), and Lemma 5.5.
  <https://arxiv.org/html/1704.03504v7>
* Zhi-Wei Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  arXiv:2609.01594v2, 2026 preprint, Proposition 2.1, Theorems 3.1 and 4.1,
  Propositions 6.1–6.2, and Section 7.
  <https://arxiv.org/html/2609.01594v2>

The local improvements below have their own proofs. The Lucas-sequence and
binomial bridge results remain explicit mathematical dependencies on Sun's
papers, including the 2026 preprint.

## 2. Fully fixed source polynomial and coefficient bound

Let `r_1,...,r_22` be the literal quadratic residuals in
`data/parent_quartic31.json`, with all four ports replaced by the **complete**
121-by-8801, 943-tile tuple. The authoritative port mapping is
`beta=beta`, `K0=K`, `MC=MC`, `MF=MF_source`; in particular, the mask port is
already shifted. Set

\[
P_0(n_1,\ldots,n_{31})=\sum_{j=1}^{22}r_j(n_1+1,\ldots,n_{31}+1)^2.
\]

The parent reduction and coefficient adapter establish
`exists n in N^31: P_0(n)=0` iff `not Con(ZFC)`. This shift is essential:
the parent's variables are positive, whereas Sun's source witnesses are
nonnegative. At the all-one parent assignment the fifth residual
`E-X(a-E)` equals 1. Therefore `P_0(0)>0`. The source degree is exactly 4.

Use the input-independent polynomial `P(a,n)=P_0(n)` and specialize **a=0**.
This represents the explicitly defined Diophantine set
`{a in N: exists n in N^31, P_0(n)=0}`. The construction does not choose
between the empty set and all of N, and does not require an index for that
set. All formulas are derived directly from the same fixed `P_0`.

Write `P=sum p_alpha a^alpha_0 n_1^alpha_1 ... n_31^alpha_31`, and let

\[
c_\alpha=(4-|\alpha|)!\prod_{j=0}^{31}\alpha_j!\,p_\alpha,
\qquad e(\alpha)=\sum_{j=0}^{31}\alpha_j5^j.
\]

All nonzero records have `alpha_0=0`. The 402 weighted coefficient recipes
are listed in `data/constants.json`. The verifier reconstructs them exactly
from the 22 shifted residuals; omitted records are zero. The positive
integer factorial multiplier gives `|p_alpha|<=|c_alpha|`.

The verified port bit lengths are `(1064921,1070004,1064921,1064922)`.
`data/index_bound.json` proves, for every weighted coefficient,

\[
|c_\alpha|+1<2^s,\qquad s=4269855.
\]

Fix the additional source constant

\[
\beta_S=2^{4269882}=2^{2\cdot2134941}.
\]

Since `48*33^4=56924208<2^27`,

\[
\beta_S>33^4\,4!\,2\max_\alpha |p_\alpha|.
\]

This is precisely Sun 2021's required `p^(alpha*p)` coefficient bound for
`p=2`, `nu=31`, `delta=4`. Its full bytes and hashes are supplied as
`data/beta_sun.bin.gz`; the other fixed leaves are literal small integers or
the supplied finite coefficient recipes.

## 3. Explicit source coding

Put `t=5^31`, `L_c=5^32=5t`. With the integer variables f,g define

\[
\begin{aligned}
b&=1+3f,&\mathcal B&=\beta_S b^4,\\
\ell&=\sum_{j=1}^{31}\mathcal B^{5^j},&
D_c&=\sum_{|\alpha|\le4}c_\alpha\mathcal B^{L_c-e(\alpha)},\\
N_0&=\mathcal B^{t+1},&N_1&=4\mathcal B^{9t+1},&N&=N_0N_1,\\
M_c&=N_0-1-(b-1)\ell,&
T_c&=M_c+(\mathcal B-2)\mathcal B^{L_c}N_0,\\
J_c&=2(1+g)^4D_c+\sum_{i=0}^{9t}\mathcal B^{i+1},&
S_c&=g+J_cN_0,\\
R_c&=(S_c+T_c+1)N+T_c+1,&
X&=(N-1)R_c,&Y&=N^2,\\
\mathscr C&=b\mathcal B^t.
\end{aligned}
\]

Every exponent and every sum limit is a fixed integer. The mask `M_c`
telescopes Sun's digit sum: all its digits are `B-1`, except positions
`5^1,...,5^31`, where the digit is `B-b`. The construction of `D_c` is
exactly the factorial-weighted reversed-base expression of Sun 2021,
Theorem 3.1. Specializing its `p=2` removes the apparent denominator `p-1`
in the formula for X. Its bound has the required form
`Ccap=2^(4269882*t)*b^(4t+1)` with fixed positive exponents.

The theorem gives the following two implications:

* From a nonnegative zero of `P_0`, choose f arbitrarily large and choose
  `b<=g<Ccap` with b both a square and a power of 2, and
  `Y` dividing `binomial(2X,X)`.
* Conversely, `f!=0`, `0<=g<2Ccap`, b a square and a power of 2, and that
  divisibility imply a nonnegative zero of `P_0`.

The size hypotheses of Sun 2026 Proposition 2.1 also hold. If `f!=0`, b is
a square and `0<=g<2Ccap`, then `b=1+3f` forces f>0 and b>=4. The proof of
Sun 2021 gives positive N, `R_c>=N+1>B>=b`; our enormous fixed base makes
`X>3b` and `Y>max(b,256)` strict. No extra normalization or additional
source witness is needed.

The circuit evaluates `D_c` by a finite shared-power Horner construction.
Its correctness can also be read from the literal 402-term sum above.
The geometric sum is computed by the division-free identities
`G_(2n)=G_n(1+B^n)` and `G_(2n+1)=G_(2n)+B^(2n)`, where
`G_n=sum_(i=0)^(n-1) B^i`. Therefore an enormous fixed degree does not
require an enormous circuit description.

## 4. The bridge and modified Lucas certificate

Introduce h,k,l,w,x,y,z,m, so the total unknowns are exactly
`f,g,h,k,l,w,x,y,z,m`. Define the following polynomials, in this order:

\[
\begin{aligned}
L&=lY,&U&=2LX,&V&=4gwY,&W&=bw,\\
A&=U(V+1),&B&=2X+1,&C&=B+(A-2)h,\\
P_n&=U^2V,&K&=X+1+k(P_n-2),\\
S&=2A-5,&T&=3WC-2(W^2-1),\\
R_2&=(P_n^2-4)K^2+4,\\
\Delta&=8\mathscr C^3gK^2-g^2\{32(C-KL)^2\mathscr C^3+g^2K^2\},\\
O&=f^2l^2\Delta,&\xi&=zx,\\
D&=(A^2-4)C^2+4,&E&=C^2D\xi,\\
F&=4(A^2-4)E^2+1,&G^*&=2(A+2)(A-2)^2E^2-1,\\
\Omega&=16E,&H^*&=C+(B-C)F+\Omega Fy,\\
I^*&=((G^*)^2-1)(H^*)^2+1.
\end{aligned}
\]

These are Sun 2026 (6.1)–(6.7), followed by (3.1)–(3.7), with its shared
witness `xi=zx`. `P_n` merely factors a repeated product. S is always a
nonzero odd integer, independently of all solution hypotheses.

Sun's positive bridge constructs f,g,h,k,l,w with b square, `R_2` square,
`S|T`, `C=u_B(A)`, and O>0. On this branch f>0, hence `b>=4` and `g>=b`.
The positive integer Delta is a multiple of g by its displayed formula,
so `Delta>=g>=4`. Since f and l are nonzero, `O=f^2l^2Delta>=4`. Alternatively,
one can start with f>=2 using the arbitrarily large source witness f.

Sun's reverse bridge states that b square, O>0, `xi!=0`, `DFI*` square,
`R_2` square, and `S|T` imply a nonnegative zero of `P_0`. Its proof first
derives `g>0`, `K!=0`, `0<g<2Ccap`, then recovers the Lucas identities and
the binomial divisibility needed in Section 3. This package invokes that
theorem with these exact formulas.

## 5. The quintic merger, including its local root proof

Let

\[
\pi(v)=(v^3-v-1)(v^2+23),\qquad
\Sigma=\xi S^5,
\]

and put

\[
r=T+Sy,\qquad
\Theta=(r^3-rS^2-S^3)(r^2+23S^2).
\]

The polynomial pi has a root modulo every positive integer. For p=23,
the cubic has the simple root 3. For odd p!=23, its discriminant is -23.
If the cubic has a root modulo p it is simple. Otherwise it is irreducible
of degree 3, and Frobenius acts on its roots as an even 3-cycle. The
discriminant is consequently a square modulo p, so `v^2+23` has a simple
root. Hensel lifting supplies roots modulo every odd prime power. For p=2,
`-23=1 mod8`, so it is a square in the 2-adic integers; this gives roots
modulo every power of 2. The Chinese remainder theorem finishes the proof.

Neither factor has a rational root. The cubic's only possible integer
roots are +/-1, neither of which vanishes, and a rational root of a monic
integer polynomial is integral. The quadratic is positive on Q.

For S!=0 and xi!=0, `S|T` implies that some residue class of y modulo xi
satisfies `Sigma|Theta`: write T=Sq and select a root c of pi modulo |xi|;
take `y=c-q mod xi`. This class can be prescribed in Sun 2026's full
residue-interpolation theorem for the Lucas certificate.

Conversely, `Sigma|Theta` forces `S|T`. If not, choose a prime p with
`alpha=v_p(S)>beta=v_p(T)`. Then `v_p(T+Sy)=beta`. In the cubic homogeneous
factor its leading term has valuation 3beta and every other term has
strictly larger valuation. Its valuation is therefore 3beta. The quadratic
factor similarly has valuation 2beta. Thus `v_p(Theta)=5beta<5alpha`,
contrary to `S^5|Theta`.

Finally Theta never vanishes over the integers when S!=0, because otherwise
`(T+Sy)/S` would be a rational root of pi. This supplies nonvanishing without
another witness. It replaces only Sun 2026's sextic merger; the residue
interpolation theorem and every bridge formula remain applicable.

## 6. Merging the two square conditions

Define

\[
r_0=b\{1+(3O-4)b^2z^2\},\qquad r_1=R_2,\qquad r_2=DFI^*.
\]

Suppose z!=0 and r_0 is an integer square. The two factors of r_0 are
coprime because the second is 1 modulo b. Also `b=1 mod3` excludes b=0
and excludes b being a negative square. If the second factor is nonzero,
coprimality and unique factorization force each factor to be a signed
square with the same sign; b must therefore be a positive square. If the
second factor is zero, coprimality forces |b|=1, and `b=1 mod3` again gives
b=1. In either case b is a positive square and
`1+(3O-4)(bz)^2` is a square. Since bz!=0, Sun's positivity lemma gives O>0.

Conversely, take positive bridge witnesses with O>=4 and b a square.
The integer `d=3O-4>0` is 2 modulo 3, hence not a square. The Pell equation
`u^2-dv^2=1` has a solution with v positive and divisible by b: take a
positive fundamental Pell unit and raise it to the finite order of its
unit class modulo b. Write v=bz with z>0. Then the bracket defining r_0
is u^2, so r_0 is a square. This positive z can be passed as the divisibility
parameter in Sun 2026 Theorem 4.1; that theorem supplies xi divisible by z
and retains free prescription of y modulo xi. Set x=xi/z.

Thus the original two square conditions can be replaced by this one
square condition, using the same existing z and the same total ten
unknowns. No new witness is hidden in r_0.

## 7. Separating weights and the radical-free final polynomial

Whenever z!=0, the actual polynomial r_0 above satisfies |r_0|>1. Indeed,
if r_0=0 then `(3O-4)b^2z^2=-1` forces |b|=1, hence b=1, f=0, O=0,
a contradiction. If r_0=+/-1, then |b|=1, again b=1 and f=O=0, whereas
`r_0=1-4z^2<=-3`.

Also, with `P_n=U^2V`,

\[
\sqrt{|r_1|}\le P_n^2+K^2+2.
\]

To verify the bound, first use `|r_1|<=(P_n^2+4)K^2+4`; subtraction of this
upper bound from `(P_n^2+K^2+2)^2` leaves
`P_n^4+K^4+P_n^2K^2+4P_n^2>=0`.

Choose the integer, possibly signed weights

\[
w_0=1,\qquad w_1=r_0,\qquad
w_2=r_0(P_n^2+K^2+3).
\]

They satisfy

\[
|w_1|>\sqrt{|r_0|},\qquad
|w_2|>\sqrt{|r_0|}+|w_1|\sqrt{|r_1|}.
\]

In the multiquadratic field generated by square roots of r_0,r_1,r_2,
suppose a signed sum of the weighted roots is rational. Any automorphism
that changes one of its nonzero root terms has a largest changed index j.
The magnitude of that term is at least |w_j|, whereas the sum of all
earlier magnitudes is strictly smaller. Its change cannot cancel. Hence
no root term can be changed, so every nonzero square root is rational.
A rational square root of an integer is integral; all three radicands
are therefore nonnegative integer squares. This argument also treats
negative radicands, using the usual complex absolute value. Zero
radicands already are squares and contribute no term.

Set

\[
X_n=\Sigma m-\Theta,\qquad A_i=\Sigma^2w_i^2r_i\quad(0\le i\le2),
\]

then define the following three expressions:

\[
V_n=X_n^2+A_2-A_0-A_1,\qquad
W_n=V_n^2+4X_n^2A_2-4A_0A_1,
\]

\[
\boxed{\ F_{10}=W_n^2-16V_n^2X_n^2A_2=0.\ }
\]

This displayed formula is radical-free and division-free. Its exact
polynomial identity is

\[
F_{10}=\prod_{\varepsilon\in\{\pm1\}^3}
\left(X_n+\sum_{i=0}^2\varepsilon_i\sqrt{A_i}\right).
\]

The right-hand side is used only to prove the identity and equivalence;
the left-hand side, composed with Sections 2–7, defines the equation.
`generated/norm3_polynomial.json` lists its 35 formal expanded terms, and
the verifier compares the circuit with all eight signed factors exactly.

## 8. Both directions and the ZFC conclusion

If `P_0` has a nonnegative zero, Section 3 and the positive bridge give
f,g,h,k,l,w with f>=2, b square, O>=4, r_1 square, `S|T`, and `C=u_B(A)`.
Section 6 gives a positive z making r_0 square. Sun 2026 Theorem 4.1,
with its divisibility parameter z, supplies positive xi divisible by z;
put x=xi/z. Choose the residue class for y from Section 5. The same
interpolation theorem gives a y in that class with r_2 square. Thus
`Sigma!=0` and `Sigma|Theta`. Select an integer m so that
`Sigma*m-Theta` equals the negative of any weighted signed sum of the
three integer roots multiplied by Sigma. One factor in the norm vanishes,
and F_10=0.

Conversely, suppose F_10=0. S is nonzero and Theta is nonzero. If Sigma=0,
then every A_i=0 and the explicit norm formula gives `F_10=Theta^8!=0`.
Thus Sigma!=0, so xi=zx!=0 and z!=0. The structural separating-weight
lemma now applies. Dividing a vanishing norm factor by Sigma shows that
a weighted signed sum of the roots of r_i is rational. Hence all three
r_i are squares, and that sum is an integer. Therefore `Sigma|Theta`.
Section 5 gives `S|T`, and Section 6 gives b square and O>0. All hypotheses
of Sun 2026 Proposition 6.2 are met; it yields a nonnegative zero of P_0.

Every step is a theorem of elementary arithmetic/number theory or of the
cited Lucas construction, formalizable in ZFC. Composing with the existing
quartic31/compiler equivalence gives the claimed ZFC equivalence to
`not Con(ZFC)`, and classical negation gives the equivalence of no
integer solutions with `Con(ZFC)`.

## 9. Reproduction and the comparison variants

Run `python build_signed10.py`, then `python verify_signed10.py` from this
directory. Only the Python standard library is required. The verifier
checks the complete coefficient reconstruction, all port and source
constant hashes, the 402 coefficient bounds, the norm identities, literal
source sums versus the optimized circuit, and degree attainment. Modular
evaluations test arithmetic transcription; they do not decide existence
of integer zeros.

The exact degree is established by a circuit upper bound and a nonzero
coefficient of that degree after substituting every unknown by one common
indeterminate, reduced modulo 101, 1009, and 1000003. One nonzero such
coefficient already proves attainment. The operation convention counts
each binary addition, subtraction, or multiplication; fixed leaves and
reuse are free, and every fixed power is expanded into binary gates.

Retained variants are:

* `signed10.json`: the structural-weight, merged-square quintic equation.
* `signed10_universal_weights.json`: same three square conditions with the
  universally separating weights `1,1+r_0^2,(1+r_0^2)(1+r_1^2)`.
* `signed10_h3quintic.json`: the merged-square equation with Sun's generic
  three-radicand weights, ordered `(r_0,DFI*,R_2)`.
* `signed10_h4quintic.json`: original four square conditions, quintic merger.
* `signed10_sun6.json`: literal Sun 2026 final formula, using four square
  conditions and `(v^2-13)(v^2-17)(v^2-221)` with degree-six homogenization.

The last variant makes the specialization independently reviewable without
any of the three local reductions. It uses exactly the same fixed source
polynomial and the same ten unrestricted integer unknowns.

