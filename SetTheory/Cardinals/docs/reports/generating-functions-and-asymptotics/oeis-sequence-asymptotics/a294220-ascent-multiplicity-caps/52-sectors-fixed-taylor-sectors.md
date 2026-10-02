# Fixed Taylor sectors and their all-orders large-cap expansions

1 October 2026. This is a separate follow-on derivation for the integral

\[
T_b=\int_0^\infty f(E_b(v))\,dv,\qquad
f(x)=\frac{\log x}{x-1},\qquad E_b(v)=\sum_{j=0}^b\frac{v^j}{j!}.
\]

It does not independently identify this integral with a combinatorial growth
constant. All assertions below hold as the integer cap \(b\to\infty\).

## 1. Precise results

Write \(R_b(v)=e^v-E_b(v)\), \(m=b+1\), and define the exact Taylor sectors

\[
A_{r,b}=\int_0^\infty a_r(e^v)R_b(v)^r\,dv,
\qquad a_r(x)=\frac{(-1)^r}{r!}f^{(r)}(x),\qquad r\ge1.
\]

They are strictly positive. For every fixed integer \(K\ge1\),

\[
T_b-\frac{\pi^2}{6}=\sum_{r=1}^K A_{r,b}
 +O_K\!\left(b^{(2-K)/2}\beta_{K+1}^{\,b}\right),
\qquad
\beta_r=\left(\frac r{r+1}\right)^r.
\tag{1}
\]

The remainder is positive and asymptotic to \(A_{K+1,b}\). In particular,
it is not merely bounded by a polynomially weakened estimate for that sector.

For every fixed \(r\ge1\) and fixed \(N\ge0\), there are rational numbers
\(c_{r,j}\), with \(c_{r,0}=1\), such that

\[
A_{r,b}=C_r b^{(3-r)/2}\beta_r^{\,b}
 \left(\sum_{j=0}^N\frac{c_{r,j}}{b^j}
       +O_{r,N}(b^{-N-1})\right),
\quad
C_r=\frac{r^{r+3/2}}{(r+1)^2}(2\pi)^{(1-r)/2}.
\tag{2}
\]

The first coefficient is

\[
c_{r,1}=\frac{3-r}{2}-\frac{r^2(r+1)}2+
 \frac{23r}{12}+\frac{13}{12r}-\frac{r+1}{r}H_r.
\tag{3}
\]

Consequently,

\[
\begin{aligned}
A_{2,b}&=\frac8{9\sqrt\pi}\sqrt b\left(\frac49\right)^b
\left(1-\frac{27}{8b}+\frac{5669}{128b^2}
-\frac{962949}{1024b^3}+O(b^{-4})\right),\\
A_{3,b}&=\frac{81\sqrt3}{32\pi}\left(\frac{27}{64}\right)^b
\left(1-\frac{43}{3b}+\frac{33952}{81b^2}
-\frac{42671116}{2187b^3}+O(b^{-4})\right).
\end{aligned}
\tag{4}
\]

The exact first sector, as derived in the first-variation audit, is

\[
A_{1,b}=(b+1)(\zeta(b+2)-1).
\tag{5}
\]

Equations (1) and (2) are fixed-sector statements. No uniformity in \(r\)
or summation of the asymptotic series over infinitely many sectors is claimed.
The bases decrease strictly to \(e^{-1}\), so infinitely many primary scales
accumulate above \(e^{-b}\).

## 2. Exact positive Taylor remainder

The integral representation

\[
f(x)=\int_0^1\frac{dt}{1-t+tx}
\]

gives

\[
a_r(x)=\int_0^1\frac{t^r\,dt}{(1-t+tx)^{r+1}}>0.
\]

Put \(x=e^v\), \(R=R_b(v)\), \(E=x-R\), and \(D=1-t+tx\).
The finite geometric identity yields

\[
f(E)-f(x)-\sum_{r=1}^K a_r(x)R^r
=R^{K+1}\int_0^1
\frac{t^{K+1}\,dt}{D^{K+1}(D-tR)}.
\tag{6}
\]

Since \(tR/D\le R/x<1\), the right side lies between

\[
a_{K+1}(x)R^{K+1}
\quad\hbox{and}\quad
\frac{x}{E}a_{K+1}(x)R^{K+1}.
\tag{7}
\]

These inequalities are pointwise; there is no exchange of asymptotic sums.
They also imply, by monotone convergence if desired, the exact identity
\(T_b-\pi^2/6=\sum_{r\ge1}A_{r,b}\) for each fixed \(b\ge2\).
This identity is not a justification for summing the large-\(b\) formulas (2).

### A uniform lower bound through \(v=b\)

The function \(e^{-v}E_b(v)\) is decreasing in \(v\), because its derivative is
\(-e^{-v}v^b/b!\). Furthermore,

\[
e^{-b}E_b(b)\ge c>0
\tag{8}
\]

uniformly for positive integer \(b\). Here is an elementary proof without a
Poisson-median theorem. Stirling gives \(p_b=e^{-b}b^b/b!\ge c_0b^{-1/2}\).
For \(0\le j\le\lfloor\sqrt b/2\rfloor\),

\[
e^{-b}\frac{b^{b-j}}{(b-j)!}
=p_b\prod_{h=0}^{j-1}(1-h/b)\ge c_1b^{-1/2};
\]

the product is bounded below by a positive absolute constant using
\(\log(1-u)\ge-2u\) for \(0\le u\le1/2\). Summing these terms proves (8)
for large \(b\), and a smaller constant handles the finitely many others.
Thus \(x/E\le c^{-1}\) throughout \(0\le v\le b\).

### The tail \(v\ge b\)

For sufficiently large \(b\), \(E_b(v)\ge v^b/b!\ge2\) there, and
\(\log E_b(v)\le v\). Hence

\[
0\le\int_b^\infty[f(E_b(v))-f(e^v)]\,dv
\le2b!\int_b^\infty v^{1-b}\,dv
=O(b^{3/2}e^{-b}).
\tag{9}
\]

Combining (7)--(9), the integrated remainder after \(K\) terms is bounded by

\[
A_{K+1,b}\ \le\ \mathcal R_{K,b}
\ \le\ c^{-1}A_{K+1,b}+O(b^{3/2}e^{-b}).
\tag{10}
\]

Since \(\beta_{K+1}>e^{-1}\), (2) proves (1). Applying (1) with \(K+1\)
also proves the sharper relation

\[
\mathcal R_{K,b}=A_{K+1,b}
\left[1+O_K\left(b^{-1/2}
  \left(\frac{\beta_{K+2}}{\beta_{K+1}}\right)^b\right)\right].
\tag{11}
\]

## 3. Isolate each sector's principal derivative exponential

A useful exact formula, obtained by changing variables in the integral for
\(a_r\), is

\[
a_r(e^v)=e^{-(r+1)v}
\frac{v-\sum_{j=1}^r(1-e^{-v})^j/j}{(1-e^{-v})^{r+1}}.
\tag{12}
\]

Its continuous value at \(v=0\) is \(1/(r+1)\). For \(v\ge1\),

\[
a_r(e^v)=e^{-(r+1)v}(v-H_r)
 +O_r((1+v)e^{-(r+2)v}).
\tag{13}
\]

Define the principal integral

\[
J_{r,b}=\int_0^\infty(v-H_r)e^{-(r+1)v}R_b(v)^r\,dv.
\tag{14}
\]

Although its integrand can be negative near zero, this does not affect its
saddle analysis. To bound the integrated error in (13), the nonnegative
power-series coefficients give

\[
R_b(v)^r\le\sum_{k\ge rm}\frac{r^k v^k}{k!}.
\]

Thus, for each fixed \(h>r\),

\[
\int_0^\infty(1+v)e^{-hv}R_b(v)^r\,dv
\le\sum_{k\ge rm}\frac{r^k}{h^{k+1}}
 \left(1+\frac{k+1}{h}\right)
=O_{r,h}\left(m\left(\frac rh\right)^{rm}\right).
\tag{15}
\]

On \([0,1]\), both derivative expressions are bounded and
\(R_b(v)\le e/m!\), giving a superexponentially small error. Consequently,

\[
A_{r,b}=J_{r,b}
 +O_r\left(m\left(\frac r{r+2}\right)^{rm}+(m!)^{-r}\right).
\tag{16}
\]

All these derivative-correction bases \((r/(r+2))^r\) are at most \(1/3\),
strictly below \(e^{-1}\). To see this, \(r\log(1+2/r)\) is increasing for
real \(r>0\), since \(\log(1+x)>x/(1+x)\); evaluate at \(r=1\).
Therefore derivative corrections are smaller than every fixed primary sector,
even after a fixed number of powers of \(b\) is included.

## 4. Uniform endpoint-tail expansion and localization

For \(s=v/m\), write

\[
R_b(ms)=\frac{(ms)^m}{m!}S_m(s),\qquad
S_m(s)=\sum_{j\ge0}s^j\prod_{i=1}^j(1+i/m)^{-1}.
\tag{17}
\]

For any fixed \(d<1\), this has a complete expansion, with every fixed
number of derivatives, uniformly on \(0\le s\le d\):

\[
S_m(s)=\sum_{j=0}^N\sigma_j(s)m^{-j}+O_{N,d}(m^{-N-1}).
\tag{18}
\]

A direct remainder proof expands
\(\prod_{i=1}^{\ell}(1+iu)^{-1}\) at \(u=0\), setting \(u=1/m\).
The absolute Taylor remainder of order \(N\) is bounded by
\(m^{-N-1}(\ell(\ell+1)/2)^{N+1}\). Summation against \(s^\ell\), or
its fixed derivatives, is uniformly bounded for \(s\le d<1\).

The exact differential equation

\[
(1-s)S_m(s)+\frac{s}{m}S_m'(s)=1
\]

then identifies all coefficients:

\[
\sigma_0(s)=\frac1{1-s},\qquad
\sigma_j(s)=-\frac{s}{1-s}\sigma_{j-1}'(s).
\tag{19}
\]

For example,
\(\sigma_1=-s/(1-s)^3\) and
\(\sigma_2=s(1+2s)/(1-s)^5\).

Substitution into (14) gives

\[
J_{r,b}=\frac{m^{rm+2}}{(m!)^r}
\int_0^\infty (s-H_r/m)S_m(s)^r e^{m\phi_r(s)}\,ds,
\quad \phi_r(s)=r\log s-(r+1)s.
\tag{20}
\]

The unique saddle is \(s_r=r/(r+1)<1\), with
\(-\phi_r''(s_r)=(r+1)^2/r\). Choose fixed \(0<a<s_r<d<1\).
On \(a\le s\le d\), use (18). The remaining ranges are exponentially smaller:

- On \(0\le s\le a\), \(S_m(s)\le(1-a)^{-1}\), and \(\phi_r\) is
  increasing up to the saddle
- On \(d\le s\le1\), the series in (17) is bounded by \(m+1\), because
  its successive-term ratio is at most \(m/(m+1)\). The phase is strictly
  below its saddle maximum
- On \(v\ge m\), \(R_b(v)\le e^v\) gives directly
  \(\int_m^\infty |v-H_r|e^{-(r+1)v}R_b(v)^r\,dv=O_r(me^{-m})\)

Stirling's bounds absorb all polynomial factors in these comparisons. This
localizes (20) to a compact interval strictly below one, where (18) and the
ordinary interior Laplace expansion are uniform to arbitrary fixed order.

## 5. Constants and a reproducible coefficient algorithm

The leading Gaussian factor in (20), including Stirling, is

\[
J_{r,b}\sim D_r m^{(3-r)/2}\beta_r^m,\qquad
D_r=r^{3/2}(r+1)^{r-2}(2\pi)^{(1-r)/2}.
\]

Since \(D_r\beta_r=C_r\), this proves the proposed constant in (2).

For the next order, put \(\lambda=(r+1)^2/r\). The leading amplitude is
\(a_0(s)=s(1-s)^{-r}\), and its next term is

\[
a_1(s)=-r s^2(1-s)^{-r-2}-H_r(1-s)^{-r}.
\]

The Laplace correction to \(a_0\) at \(s=s_r\) is

\[
\frac{a_0''}{2\lambda}
+\frac{a_0'\phi_r'''}{2\lambda^2}
+\frac{a_0\phi_r''''}{8\lambda^2}
+\frac{5a_0(\phi_r''')^2}{24\lambda^3}.
\]

Adding \(a_1\), dividing by \(a_0\), and including the Stirling correction
\(-r/12\), gives the relative coefficient in \(1/m\):

\[
d_{r,1}=-\frac{r^2(r+1)}2+\frac{23r}{12}
+\frac{13}{12r}-\frac{r+1}{r}H_r.
\]

The conversion \(m=b+1\) adds \((3-r)/2\), proving (3).

For arbitrary order, the companion script uses exact rational arithmetic:

1. Set \(z=m^{-1/2}\), \(s=s_r+uz\), and expand (19)
2. Multiply the amplitude \((s-H_rz^2)S_m(s)^r\) by the exponential of
   the higher phase terms
   \(\sum_{k\ge3}r(-1)^{k-1}(u/s_r)^kz^{k-2}/k\)
3. Include Stirling via the exponential
   \(-r\sum_{k\ge1} B_{2k}z^{4k-2}/[2k(2k-1)]\)
4. Take Gaussian moments: odd powers of \(u\) vanish and
   \(u^{2j}\) becomes \((2j-1)!!/\lambda^j\)
5. Divide by the leading amplitude and substitute \(m=b+1\)

For any requested finite order, these are finite algebraic operations. The
localization and uniform remainder arguments above establish that the resulting
formal coefficients are genuine asymptotic coefficients.

## 6. Numerical checks and scope of use

Run `python fixed-sector-verify.py --order 3 --numerics` to reproduce
`fixed-sector-validation.json`. The exact coefficient check returns zeros for
every computed positive power of \(1/m\) in sector one, consistent with
\(J_{1,b}=m/2^{m+1}\) exactly.

Some scaled principal-integral values are

| b | J₂ divided by its leading term | J₃ divided by its leading term |
|---:|---:|---:|
| 50 | 0.94532581208112154294 | 0.80732730946696633054 |
| 100 | 0.96994392414322541536 | 0.88628744312026242484 |
| 200 | 0.98412942249773838469 | 0.93694394210295266327 |
| 500 | 0.99342004902961924418 | 0.97287141516346868116 |

The script also integrates exact sectors via (12), with the cancellation-free
hypergeometric representation near zero. Numerical checks support the formulas
but are not substitutes for the proof.

### An essential asymptotic-scale warning

Equation (1) requires exact sectors (or approximations accurate on the next
exponential scale). If each \(A_{r,b}\) is replaced by only \(N_r+1\) terms of
(2), the justified additional error is

\[
O\!\left(\sum_{r=1}^K
 b^{(3-r)/2-N_r-1}\beta_r^b\right).
\]

For any fixed \(N_r\), this algebraic truncation error in an earlier sector
generally dominates every later exponential sector. Thus, for example, a few
terms of the \(A_2\) expansion do not justify numerically isolating \(A_3\).
Subtract exact \(A_2\) for that purpose. No optimal truncation, summability,
uniform sector-index estimates, or expansion at the accumulation scale
\(e^{-b}\) is established here. Likewise, reciprocation or inversion must keep
these remainder distinctions; it cannot mix finite algebraic truncations and
exponentially finer claims without an additional argument.
