# Independent audit: explicit large-cap remainder and integer inversion

Audited 1 October 2026 against `large-cap-proposal.md`, `large-cap-asymptotic.md`, and `large-cap-audit.md`.

## Verdict

The proposed exact first-variation correction and remainder are correct:

\[
 T_b=A+L_b+H_b,\qquad A=\frac{\pi^2}{6},\qquad
 L_b=(b+1)(\zeta(b+2)-1),
\]
\[
 \boxed{\quad 0\le H_b\le160b^{5/2}(4/9)^b\quad(b\ge3).\quad}
\]

The constant 160 is deliberately conservative. No numerical quadrature or unproved asymptotic estimate is used below.

The reciprocal has explicit error brackets. The Lambert-W inversion must retain an integer bracket; unconditional rounding by the ceiling of the leading-model solution is false at arbitrarily small tolerances. In fact, a slightly sharper one-sided bracket is available:

\[
 \boxed{\quad
 \lfloor b_0\rfloor+1\le b_\varepsilon
 \le\left\lceil b_0+2000b_0^{3/2}(8/9)^{b_0}\right\rceil
 \quad(b_0\ge13).
 \quad}
\]

Here all quantities and hypotheses are defined below. These statements concern the explicit integral. Applying them to a combinatorial growth constant requires the separately established identification of that constant with \(1/T_b\).

## 1. Definitions and elementary facts

For an integer \(b\ge2\), put

\[
 E_b(v)=\sum_{k=0}^b\frac{v^k}{k!},\quad
 R_b(v)=e^v-E_b(v),\quad
 f(z)=\frac{\log z}{z-1},\quad
 T_b=\int_0^\infty f(E_b(v))\,dv.
\]

The value \(f(1)=1\) is interpreted continuously. The representation

\[
 f(z)=\int_0^1\frac{dt}{1+t(z-1)}
\]

shows \(f'<0\), \(f''>0\) on \([1,\infty)\). The integral defining \(T_b\) converges for \(b\ge2\), since its integrand is \(O(\log v/v^b)\) at infinity. Also

\[
 \int_0^\infty f(e^v)\,dv
 =\int_0^\infty\frac{v}{e^v-1}\,dv
 =\sum_{j\ge1}\frac1{j^2}=A.
\]

The exchange here is Tonelli's theorem. Define

\[
 \Delta_b(v)=f(E_b(v))-f(e^v),\qquad
 \ell_b(v)=-f'(e^v)R_b(v).
\]

Convexity gives \(0\le\ell_b\le\Delta_b\). Therefore

\[
 T_b-A=L_b+H_b,\qquad
 L_b=\int_0^\infty\ell_b(v)\,dv,\qquad
 H_b=\int_0^\infty(\Delta_b(v)-\ell_b(v))\,dv\ge0.
\]

## 2. Exact evaluation of the linear term

For every \(v>0\), the absolutely convergent geometric-series derivative gives

\[
 -f'(e^v)=\sum_{h\ge2}((h-1)v-1)e^{-hv}.
\]

Although the individual terms can have either sign, multiplication by
\(R_b(v)=\sum_{k\ge b+1}v^k/k!\) and integration are justified by absolute integrability. Indeed,

\[
 \int_0^\infty |(h-1)v-1|e^{-hv}\frac{v^k}{k!}\,dv
 \le\frac{(h-1)(k+1)+h}{h^{k+2}}
 \le\frac{k+2}{h^{k+1}}.
\]

For \(k\ge b+1\ge3\),

\[
 \sum_{h\ge2}\frac{k+2}{h^{k+1}}
 \le (k+2)2^{-(k-1)}\sum_{h\ge2}h^{-2},
\]

and the resulting sum over \(k\) is finite. The single endpoint \(v=0\) is immaterial. Fubini now gives

\[
 L_b=\sum_{h\ge2}\sum_{k\ge b+1}
 \frac{(h-1)k-1}{h^{k+2}}.
\]

Writing \(n=b+1\) and summing the geometric derivative yields

\[
 \sum_{k\ge n}\frac{(h-1)k-1}{h^{k+2}}
 =\frac{n}{h^{n+1}}.
\]

Consequently

\[
 \boxed{L_b=(b+1)(\zeta(b+2)-1).}
\]

## 3. Explicit bound for the nonlinear remainder

### 3.1 A derivative bound valid down to \(z=1\)

For all \(z\ge1\),

\[
 0<f''(z)\le\frac{16(1+\log z)}{z^3}.                 \tag{1}
\]

For \(1\le z\le2\), the integral representation gives \(f''(z)\le2/3\), whereas the right side is at least \(16/8=2\). For \(z\ge2\), use

\[
 f''(z)=\frac{2\log z-3+4/z-1/z^2}{(z-1)^3}
 \le\frac{2\log z}{(z-1)^3}
 \le\frac{16\log z}{z^3}.
\]

### 3.2 The interval \(0\le v\le b\)

The derivative identity

\[
 \frac{d}{dv}\big(e^{-v}E_b(v)\big)=-e^{-v}\frac{v^b}{b!}
\]

shows that \(e^{-v}E_b(v)\) decreases. The classical upper Stirling inequality implies the convenient crude bound

\[
 b!\le\sqrt{2\pi b}(b/e)^b e^{1/(12b)}
 \le3\sqrt b\,(b/e)^b\qquad(b\ge1).
\]

Thus, throughout \(0\le v\le b\),

\[
 E_b(v)e^{-v}\ge E_b(b)e^{-b}
 \ge e^{-b}\frac{b^b}{b!}\ge\frac1{3\sqrt b}.
\]

In Taylor's theorem, the intermediate argument \(\xi\) lies between \(E_b(v)\) and \(e^v\). Hence \(\log\xi\le v\), \(\xi^{-3}\le27b^{3/2}e^{-3v}\), and (1) gives

\[
 0\le\Delta_b(v)-\ell_b(v)
 \le216b^{3/2}(1+v)e^{-3v}R_b(v)^2.                 \tag{2}
\]

To integrate this bound, all terms are nonnegative. Group the square of \(R_b\) by total degree \(S\). The bound on the restricted binomial sum is

\[
 \sum_{k=b+1}^{S-b-1}\binom Sk\le2^S,
 \qquad S\ge2b+2.
\]

It follows that

\[
 \begin{aligned}
 I_b&:=\int_0^\infty(1+v)e^{-3v}R_b(v)^2\,dv\\
 &\le\sum_{S\ge2b+2}\frac{S+4}{9}(2/3)^S\\
 &=\frac{8(b+4)}{27}(4/9)^b.
 \end{aligned}
\]

Integrating (2) over \([0,b]\) therefore gives

\[
 \int_0^b(\Delta_b-\ell_b)\,dv
 \le64b^{3/2}(b+4)(4/9)^b.                         \tag{3}
\]

### 3.3 The interval \(v\ge b\)

For \(b\ge3\) and \(v\ge b\),

\[
 E_b(v)\ge\frac{v^b}{b!}\ge\frac{b^b}{b!}\ge\frac{27}{6}>2.
\]

The sequence \(b^b/b!\) is increasing, which verifies the last inequality for every such \(b\). Using \(\log E_b(v)\le v\),

\[
 0\le\Delta_b(v)-\ell_b(v)\le\Delta_b(v)
 \le f(E_b(v))\le2b!v^{1-b}.
\]

Consequently

\[
 \begin{aligned}
 \int_b^\infty(\Delta_b-\ell_b)\,dv
 &\le\frac{2b!b^{2-b}}{b-2}\\
 &\le\frac{6b^{5/2}}{b-2}e^{-b}
 \le6b^{5/2}(4/9)^b.                              \tag{4}
 \end{aligned}
\]

The final inequality uses \(b-2\ge1\) and \(e^{-1}<4/9\). This argument directly bounds the Taylor remainder, so no separate estimates of a signed linear tail are needed.

Combining (3) and (4), and using \(1+4/b\le7/3\), gives

\[
 H_b\le\left(64\cdot\frac73+6\right)b^{5/2}(4/9)^b
 <160b^{5/2}(4/9)^b.
\]

This completes the stated remainder proof.

## 4. Reciprocal: exact and asymptotic error brackets

Put

\[
 B_b=160b^{5/2}(4/9)^b,\quad \mu_b=1/T_b,\quad
 d_b=1/A-\mu_b.
\]

Since \(x\mapsto x/[A(A+x)]\) is increasing for \(x\ge0\),

\[
 \boxed{\frac1{A+L_b+B_b}\le\mu_b\le\frac1{A+L_b},}
\]
\[
 \boxed{\frac{L_b}{A(A+L_b)}\le d_b
 \le\frac{L_b+B_b}{A(A+L_b+B_b)}.}
\]

In particular, a useful additive bracket around the exact zeta correction is

\[
 -\frac{L_b^2}{A^2(A+L_b)}
 \le d_b-\frac{L_b}{A^2}
 \le\frac{B_b}{A^2}.                              \tag{5}
\]

For completeness, integral comparison gives

\[
 L_b\le(b+3)2^{-b-2}\le\frac b2\,2^{-b}\qquad(b\ge3).
\]

It follows that the absolute value of the left error bound in (5) is smaller than \(B_b/A^2\). Thus

\[
 \left|d_b-\frac{(b+1)(\zeta(b+2)-1)}{A^2}\right|
 \le\frac{160}{A^2}b^{5/2}(4/9)^b.                \tag{6}
\]

To isolate the leading exponential, define

\[
 M_b=(b+1)2^{-b-2},\quad V_b=L_b-M_b,\quad
 D=\frac1{4A^2}=\frac9{\pi^4},\quad
 g(x)=D(x+1)2^{-x}.
\]

Another integral comparison gives

\[
 (b+1)3^{-b-2}\le V_b\le(b+4)3^{-b-2}.
                                                                    \tag{7}
\]

### A strict sign that is helpful at integer jumps

For every integer \(b\ge3\),

\[
 \boxed{d_b>g(b).}                                      \tag{8}
\]

Indeed, \(d_b\ge L_b/[A(A+L_b)]>M_b/A^2\) is equivalent to \(AV_b>M_bL_b\). The preceding bounds imply

\[
 \frac{M_bL_b}{V_b}\le\frac{9b}{8}(3/4)^b
 \le\frac{729}{512}<\frac32<A.
\]

The middle maximum is attained at \(b=3,4\); successive ratios of \(b(3/4)^b\) are \(3(b+1)/(4b)\le1\) for \(b\ge3\). This proves (8).

On the other side, \(d_b\le(L_b+B_b)/A^2\), while (7) implies \(V_b\le b^{5/2}(4/9)^b\). Therefore the leading approximation has the explicit one-sided error

\[
 \boxed{0<d_b-g(b)
 \le\frac{161}{A^2}b^{5/2}(4/9)^b\qquad(b\ge3).}       \tag{9}
\]

Dividing by \(g(b)=(b+1)2^{-b}/(4A^2)\) yields

\[
 \boxed{0<\frac{d_b}{g(b)}-1
 \le644b^{3/2}(8/9)^b\qquad(b\ge3).}                 \tag{10}
\]

In particular,

\[
 T_b-A\sim(b+1)2^{-b-2},\qquad
 1/A-1/T_b\sim\frac{9(b+1)}{\pi^4 2^b},
\]

with the claimed additive \(O(b^{5/2}(4/9)^b)\) error for the reciprocal as well.

## 5. A rigorous integer-cap Lambert-W inversion

Because \(E_{b+1}(v)>E_b(v)\) for \(v>0\) and \(f\) is strictly decreasing, \(T_b\) strictly decreases, \(\mu_b\) strictly increases, and \(d_b\) strictly decreases to zero. Thus, for every \(\varepsilon>0\), the integer threshold

\[
 b_\varepsilon=\min\{b\in\mathbb Z:\ b\ge2,\ 
           \mu_b\ge1/A-\varepsilon\}
 =\min\{b\ge2:\ d_b\le\varepsilon\}
\]

exists.

For sufficiently small \(\varepsilon\), let \(b_0\) be the real solution of \(g(b_0)=\varepsilon\) on the decreasing branch. Writing \(a=\log2\), one obtains

\[
 \boxed{b_0=-\frac{W_{-1}(-\varepsilon a/(2D))}{a}-1.}       \tag{11}
\]

Here \(W_{-1}\) denotes the real branch with values at most \(-1\). Formula (11) is merely an exact inversion of the real leading model \(g\); it does not define any real interpolation of the sequence \(T_b\).

An explicit sufficient hypothesis for the bracket below is

\[
 0<\varepsilon\le g(13),\qquad\text{equivalently } b_0\ge13.
\]

Set

\[
 \phi(x)=x^{3/2}(8/9)^x,\qquad \delta(x)=2000\phi(x).
\]

The function \(\phi\) is decreasing on \([13,\infty)\), since

\[
 (\log\phi)'(x)=\frac{3}{2x}-\log(9/8)<0.
\]

One exact verification is \(\log(9/8)>2/17>3/26\). Also, for \(x\ge2\),

\[
 (\log g)'(x)=\frac1{x+1}-\log2<-\frac13,
\]

using \(\log2>2/3\).

For the lower bound, any integer \(3\le b\le b_0\) satisfies \(d_b>g(b)\ge\varepsilon\) by (8). The integer 2 is also excluded, since \(d_2>d_3>g(3)>g(b_0)\). Hence

\[
 b_\varepsilon\ge\lfloor b_0\rfloor+1.                 \tag{12}
\]

For the upper bound take \(m=\lceil b_0+\delta(b_0)\rceil\). By (10), monotonicity of \(\phi\), and the logarithmic slope estimate,

\[
 \begin{aligned}
 \frac{d_m}{\varepsilon}
 &\le e^{-(m-b_0)/3}\bigl(1+644\phi(m)\bigr)\\
 &\le e^{-2000\phi(b_0)/3}\bigl(1+644\phi(b_0)\bigr)<1.
 \end{aligned}
\]

The strict final inequality follows from \(\log(1+y)\le y\) and \(2000/3>644\). Therefore \(b_\varepsilon\le m\). Combining this with (12) proves

\[
 \boxed{\lfloor b_0\rfloor+1\le b_\varepsilon
 \le\lceil b_0+2000b_0^{3/2}(8/9)^{b_0}\rceil
 \quad(b_0\ge13).}                                   \tag{13}
\]

This is stronger than the proposed symmetric bracket; in particular it implies

\[
 \left\lceil b_0-2000b_0^{3/2}(8/9)^{b_0}\right\rceil
 \le b_\varepsilon\le
 \left\lceil b_0+2000b_0^{3/2}(8/9)^{b_0}\right\rceil.
\]

The constants make these enclosures conservative at moderate \(b_0\), but their width in the real variable tends to zero exponentially. The ceilings must not be discarded.

### Why unconditional ceiling is actually false

Choose any integer \(n\ge3\) and set \(\varepsilon=g(n)\). Then \(b_0=n\), but (8) gives \(d_n>\varepsilon\), so \(b_\varepsilon\ge n+1\). Thus \(b_\varepsilon=\lceil b_0\rceil\) fails along a sequence of tolerances tending to zero. For all sufficiently large \(n\), \(\delta(n)<1\), and (13) gives the exact value \(b_\varepsilon=n+1\) at those model jump points.

Away from an integer boundary, (13) can certify the usual ceiling: if \(b_0\) is nonintegral and \(\delta(b_0)\le\lceil b_0\rceil-b_0\), both bounds in (13) equal \(\lceil b_0\rceil\).

## Scope of this audit

The exact zeta first variation, the stated exponential-order remainder, the reciprocal brackets, and the integer inversion are proved above. No higher nonlinear-sector coefficient or all-orders expansion is asserted here. The previously audited first-equivalence argument is consistent with this stronger result.
