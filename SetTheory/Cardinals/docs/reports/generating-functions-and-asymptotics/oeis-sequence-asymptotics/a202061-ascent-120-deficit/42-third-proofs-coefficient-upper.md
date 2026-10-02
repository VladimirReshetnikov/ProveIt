# Independent proof audit: the next one-sided global deficit constant

Date: 2 October 2026. This is new, separately audited research. It does not change the frozen second-order release, and it does not assert a matching lower coefficient estimate.

## Verdict and precise scope

The candidate in `../a202061-third-order-research/root-sharp-upper-plan.md` can be completed. The quantitative arguments below establish

\[
D_n\ge C F\left[1+\frac{7\log L}{3L}+\frac{\kappa}{L}\right]+o(F/L),
\qquad L=\log n,\quad F=n^{1/3}L^{2/3},
\tag{T}
\]

where

\[
B_0=\alpha/3,\quad Y_0=(2vB_0/\pi^2)^{1/3},\quad
C=3B_0/Y_0,\quad
\kappa=\log Y_0-2\log3+2c_*.
\]

Here \(D_n=n\log\mu-\log a_n\), and \(c_*\) is the exact row-amplitude constant defined below. In particular, this is a coefficient **upper** bound, or deficit **lower** bound. It does not establish equality with the right side through order \(F/L\). No multiplicative coefficient equivalent is asserted.

The imported inputs are the exact positive macro-kernel and terminal representation, its uniform square-root transfer with analytic parameter derivatives, the critical root derivative identities, and the fixed-ceiling first-hit estimate. These inputs have already been independently audited in the sharp-deficit and second-order packages. The finite-height spectral comparison is not needed here: only the exact row mass and tail amplitude are used. This note supplies the previously missing quantitative row estimate and the next-order integrated calibration estimate.

One correction to the candidate's wording is necessary. Although the endpoint geometric sum has relative error \(O(1/\log r)\), its conversion to \(2e^c\) has error \(O(\log\log r/\log r)\). In our range this is \(O(\log L/L)\), which is still \(o(L^{-1/4})\).

## 1. Exact analytic input and amplitude

Let \(z\) be the smallest positive root of \(z^3-5z^2+6z-1=0\), and set

\[
\rho=3z^2-10z+2,\quad t=z^{-1},\quad
\alpha=(8z^2-29z+9)/7,\quad v=(2z^2-7z+2)/2.
\]

For the exact critically tilted macro-step weights \(w(e,q,d)\), define

\[
W_q(\sigma,\theta)=\sum_{e,d}w(e,q,d)e^{\sigma e+\theta d}.
\]

There is one fixed parameter neighborhood such that

\[
W_q(\sigma,\theta)
 =a(\sigma,\theta)q^{-3/2}e^{q\Psi(\sigma,\theta)}
   (1+E_q(\sigma,\theta)),\qquad
|\partial^j E_q|\le C_j/q\quad (0\le j\le4),
\tag{1}
\]

uniformly for sufficiently large \(q\); finitely many remaining \(q\) are analytic in that same neighborhood. The amplitude is analytic and positive at the origin. The root expansion is

\[
\Psi(\sigma,\theta)
 =\frac{\sigma+v\theta^2/2}{\alpha}
   +O(\sigma^2+|\sigma\theta|+|\theta|^3).
\tag{2}
\]

The exact mass and amplitude are

\[
m_*:=\sum_{q\ge1}W_q(0,0)=\frac{\rho}{(1-\rho)z+\rho}<1,
\]
\[
C_q=\frac{\sqrt{-16z^2+55z-10}}{2\sqrt\pi},\qquad
 a_*:=a(0,0)=\frac{\rho C_q}{(1-\rho)z},\qquad
 c_*:=\log\frac{1-m_*}{2a_*}.
\tag{3}
\]

For clarity, the amplitude is that of the actual macro-kernel, including its factor \(\rho t/(1-\rho)\). Omitting the factor \(t\) would change the constant in (T).

These formulas can also be recovered directly from the quadratic for \(Q\). With \(b=1-x\),

\[
\mathcal B=b(\zeta-b)+xT(x-\zeta),\qquad
\Delta=\mathcal B^2-4xT(1-\zeta)b\zeta,
\]

and smaller discriminant root \(z_c\), the square-root singular amplitude is

\[
C_q(x,T)=\frac{\sqrt{-z_c\Delta_\zeta(x,z_c,T)}}
 {4\sqrt\pi xT(1-z_c)}.
\]

Substituting \((x,T,z_c)=(\rho,z^{-1},z)\) and reducing modulo the cubic gives (3). Also, at the root,

\[
\frac{xT}{1-x}Q(x,z,T)
 =-\frac{\mathcal B(x,z,T)}{2(1-x)(1-z)},
\]

which reduces to the stated \(m_*\). The exact algebra and numerical evaluation are independently replayed by `check_constants.py` in this directory. They do not replace the analytic proof.

## 2. Quantitative head estimate

For real \((\sigma,\theta)\) with \(Q(|\sigma|+|\theta|)=o(1)\), differentiating (1) along the line segment from the origin gives

\[
|\nabla W_q(\sigma',\theta')|\le Cq^{-1/2},\qquad 1\le q\le Q,
\]

uniformly on that segment. Indeed, derivatives of \(a\) and \(E_q\) are bounded, derivatives of \(e^{q\Psi}\) supply at most a factor \(Cq\), and the exponential remains bounded since \(|q\Psi|\le C Q(|\sigma|+|\theta|)=o(1)\). The finitely many small indices are absorbed by analyticity. Therefore

\[
\sum_{q\le Q}W_q(\sigma,\theta)
 \le \sum_{q\le Q}W_q(0,0)
      +C(|\sigma|+|\theta|)\sqrt Q
 \le m_*+C(|\sigma|+|\theta|)\sqrt Q.
\tag{4}
\]

This is a quantitative bound for an increasing head cutoff. No unspecified finite-cutoff continuity is used.

## 3. Uniform endpoint-tail lemma

Put \(\ell=\log L\),

\[
H=n^{2/3}L^{1/3},\quad \epsilon=L^{-12},\quad Q=\lceil L^4\rceil,
\]

and suppose

\[
\epsilon H\le r\le (R+1)H,\qquad
k_r=\tfrac12\log r+\log\log r+c,
\]

where \(R\) is fixed and \(c\) remains in a fixed compact interval. Uniformly in these choices,

\[
\sum_{Q<q\le r}q^{-3/2}e^{k_rq/r}
 =2e^c+O\!\left(\frac{\ell}{L}+L^{-2}
                  +n^{-1/6}L^5\right).
\tag{5}
\]

Only the upper-bound version of (5) is needed; the equality follows from the same splitting.

To prove it, note that \(\log r=(2/3)L+O(\ell)\) uniformly and split the sum at \(r/L^2\) and \(r/2\). For large \(n\), these points exceed \(Q\).

* On \(Q<q\le r/L^2\), the exponential is at most \(e^{C/L}\), so the sum is \(O(Q^{-1/2})=O(L^{-2})\).
* On \(r/L^2<q\le r/2\), the sum is bounded by
  \[
  C\frac{L}{\sqrt r}e^{k_r/2}
  \le C L^{3/2}r^{-1/4}
  \le C n^{-1/6}L^5.
  \]
* On \(r/2<q\le r\), write \(q=\lfloor r\rfloor-j\). The geometric distribution proportional to \(e^{-k_rj/r}\) has mean \(O(r/k_r)\). On the retained range, the factor \((q/r)^{-3/2}\) differs from 1 by at most a constant times \((r-q)/r\). Summing this bound gives
  \[
  \sum_{r/2<q\le r}q^{-3/2}e^{k_rq/r}
  =\frac{r^{-1/2}e^{k_r}}{k_r}
    \left[1+O(k_r^{-1}+k_r/r)\right].
  \tag{6}
  \]
  The geometric tail beyond this range is exponentially small in \(k_r\); nonintegral \(r\) changes the answer by relative \(O(k_r/r)\). Since
  \[
  \frac{r^{-1/2}e^{k_r}}{k_r}=e^c\frac{\log r}{k_r}
  =2e^c\left[1+O\!\left(\frac{\log\log r}{\log r}\right)\right],
  \]
  this is \(2e^c+O(\ell/L)\).

In particular, the error in (5) is \(o(L^{-1/4})\).

## 4. Refined potential and exact finite-n calibration

Use two different names for the cutoffs:

\[
\delta=\epsilon=L^{-12},\qquad d_n=L^{-1/4},\qquad
\tau=1-2\delta,\qquad a=\alpha/(2L).
\]

Here \(d_n\) is a row-mass slack, not the endpoint cutoff. Define

\[
V_n(y)=\frac{\alpha}{L(y+\epsilon)}
 \left[\frac12\log(H(y+\epsilon))
       +\log\log(H(y+\epsilon))+c_*-d_n\right],\quad 0\le y\le R,
\tag{7}
\]

and

\[
B=B_0+a\left[\frac73\ell+2\log(2/3)+2c_*-2d_n\right].
\tag{8}
\]

For large \(n\), \(B\) lies in a fixed compact subset of \((0,\infty)\). Let \(p_*\) be the full Kepler momentum for this \(B\), with

\[
y_*(x)=Y\sin^2 u,\quad x=(u-\sin u\cos u)/\pi,\quad
Y=(2vB/\pi^2)^{1/3},\quad
p_*=-y_*'/v,\quad p_*'=B/y_*^2.
\]

Set

\[
p_n(s)=p_*(\delta+\tau s),\quad A(s)=p_n'(s)>0,\quad
J_n(A)=\min_{0\le y\le R}(Ay+V_n(y)),
\]

and choose \(g_n(1)=0\), \(g_n'=vp_n^2/2-J_n(p_n')\). Then

\[
f_n(s,y)=g_n(s)+p_n(s)y
\]

obeys the exact inequality

\[
-\partial_sf_n+\frac v2(\partial_yf_n)^2
 =J_n(A)-Ay\le V_n(y).
\tag{9}
\]

The potential is strictly convex for large \(n\): its second derivative has leading positive term proportional to \(\log(H(y+\epsilon))/(L(y+\epsilon)^3)\), while all remaining terms are smaller uniformly. Hence \(J_n\) is \(C^1\), including any boundary regimes, and \(0\le J_n'\le R\). The same exact estimates as in the audited second-order proof give

\[
\|p_n\|_\infty=O(L^4),\quad
\|p_n'\|_\infty=O(L^{16}),\quad
\|p_n''\|_\infty=O(L^{28}),
\]
\[
\|f_n\|_{C^2}=O(L^{28}),\quad
\|(f_n)_s\|_\infty=O(L^{16}),\quad
\|(f_n)_y\|_\infty=O(L^4).
\tag{10}
\]

For example, \(g_n''=vp_np_n'-J_n'(p_n')p_n''\); no second derivative of the optimizer is required.

## 5. Uniform Legendre expansion, including the cutoff endpoints

For \(u=y+\epsilon\), an exact rearrangement of (7) is

\[
V_n(y)=\frac{B+a\log u+R_n(u)}u,
\]
\[
R_n(u)=2a\log\left(1+\frac{\ell+3\log u}{2L}\right).
\tag{11}
\]

On \(\epsilon\le u\le R+\epsilon\), the logarithm's argument is positive and uniformly tends to 1. In this range,

\[
|R_n(u)|\le C\frac{\ell+|\log u|}{L^2},\qquad
|(u\partial_u)^jR_n(u)|\le C/L^2\quad (j=1,2).
\tag{12}
\]

Let \(\lambda=\sqrt{B/A}\), for \(A=A(s)\) along the truncated arch. Because \(A=\tau B/y_*^2\),

\[
\lambda=\frac{y_*(\delta+\tau s)}{\sqrt\tau},\qquad
cL^{-8}\le\lambda\le C_1.
\tag{13}
\]

Choose the fixed \(R\) large enough that \(\lambda\le(R+\epsilon)/3\) for all large \(n\). Also \(\epsilon/\lambda=O(L^{-4})\). Consequently the admissible domain for \(r=u/\lambda\) contains \([1/2,2]\), and \(|\log\lambda|=O(\ell)\) uniformly.

After adding \(\epsilon A\) and dividing the objective by \(\sqrt{BA}\), the minimization becomes

\[
\Phi(r)=r+\frac1r+
 \frac{a}{B}\frac{\log\lambda+\log r}{r}
 +\frac{R_n(\lambda r)}{Br}.
\tag{14}
\]

Globally on its admissible domain, \(B+a\log u+R_n(u)\ge B/2\) for large \(n\). Thus \(\Phi(r)\ge r+1/(2r)\), which is at least 4 outside \([1/8,8]\). At \(r=1\), \(\Phi(1)=2+o(1)\). Therefore its minimizer belongs to \([1/8,8]\). On that fixed interval the perturbation and its first two derivatives are bounded by

\[
C\left[\frac{1+|\log\lambda|}{L}
       +\frac{\ell+|\log\lambda|}{L^2}\right]=o(1).
\]

The strict separation of \(r+1/r\) from 2 outside \([1/2,2]\) then puts the minimizer in \((1/2,2)\). It is an interior minimizer of the original constrained problem. The derivative equation, and the lower bound for \(2r^{-3}\) on this compact interval, give

\[
r_{\min}=1+O((1+|\log\lambda|)/L).
\tag{15}
\]

Taylor expansion at 1, using (12), now proves the genuinely uniform value estimate

\[
J_n(A)=2\sqrt{BA}-\epsilon A
       +a\frac{\log\lambda}{\lambda}
       +O\left(\frac{\sqrt A}{L^2}
          [1+\log^2 A+\ell]\right).
\tag{16}
\]

In particular the perturbation's square, which could have mattered after endpoint integration, is retained explicitly.

For \(j=0,1,2\), the Kepler endpoint estimates give

\[
\int_0^1\sqrt{A(s)}\,[1+|\log A(s)|^j],ds=O(1).
\tag{17}
\]

To check this uniformly, change variables to \(x=\delta+\tau s\). Near either endpoint, the full-arch comparison is \(x^{-2/3}(1+|\log x|^j)\), which is integrable; reparameterization changes the bounds only by fixed factors. Therefore the integrated error in (16) is

\[
O((1+\ell)/L^2)=o(1/L).
\tag{18}
\]

Also

\[
\epsilon\int_0^1A(s)\,ds
 =\epsilon[p_n(1)-p_n(0)]=O(L^{-8}).
\tag{19}
\]

The complete-arch action is

\[
\int_0^1[2\sqrt{Bp_*'}-vp_*^2/2],dx=3B/Y=:C(B).
\]

Cutting off its two ends and applying the factors \(\tau^{-1/2}\) and \(\tau^{-1}\) changes the action by \(O(\delta^{1/3})=O(L^{-4})\). This follows by separately bounding both discarded integrands by \(Cx^{-2/3}\).

Finally,

\[
\int_0^1\frac{\log\lambda(s)}{\lambda(s)}\,ds
 =\frac1{\sqrt\tau}\int_\delta^{1-\delta}
  \frac{\log y_*(x)-\tfrac12\log\tau}{y_*(x)},dx
\]
\[
 =\frac2Y(\log Y-2\log2)
  +O(\delta^{1/3}(1+|\log\delta|)).
\tag{20}
\]

Indeed, \(dx/y_*=2\,du/(\pi Y)\), and
\(\int_0^\pi\log\sin u\,du=-\pi\log2\). The omitted logarithmic endpoint integrals are \(O(\delta^{1/3}(1+|\log\delta|))\), by the same integrable comparison.

Integrating (16) now yields

\[
f_n(0,0)=C(B)+a\frac2{Y(B)}(\log Y(B)-2\log2)
          +O\!\left(\frac{1+\ell}{L^2}+L^{-4}\right).
\tag{21}
\]

Since \(C'(B)=2/Y(B)\) and \(C=\alpha/Y_0\), Taylor expansion of (21) at \(B_0\) gives

\[
f_n(0,0)=C\left[1+\frac{7\ell}{3L}
                      +\frac{\log Y_0-2\log3+2c_*}{L}
                      -\frac{2d_n}{L}\right]
             +O\!\left(\frac{(1+\ell)^2}{L^2}+L^{-4}\right).
\tag{22}
\]

The identity \(2\log(2/3)-2\log2=-2\log3\) is the source of the constant in (T). The slack costs \(2Cd_n/L=2CL^{-5/4}=o(1/L)\).

## 6. Quantitatively contracting transformed rows

Retain source and destination heights in \([1,RH]\), and legal steps satisfying \(q\le h\) and \(k+e\le n-1\). Let \(s=k/n\), \(y=h/H\),

\[
\eta=F/n,\qquad \beta=F/H,\qquad \beta^2=\eta,\quad \eta H=L.
\]

The transformed step has weight

\[
w(e,q,d)\exp\{F[f_n(s,y)-f_n(s+e/n,y+d/H)]\}.
\tag{23}
\]

On \(e\le HL^{40}\), \(|d|\le\sqrt H L^{40}\), use (10) and the fact that \(f_n\) is affine in height. The Taylor remainder is at most

\[
CFL^{28}\left[(HL^{40}/n)^2
 +(HL^{40}/n)(L^{40}/\sqrt H)\right]
 \le Cn^{-1/3}L^{110}.
\tag{24}
\]

The linear tilts are

\[
\sigma=-\eta(f_n)_s,\qquad \theta=-\beta p_n,
\]

so \(|\sigma|\le Cn^{-2/3}L^{50/3}\),
\(|\theta|\le Cn^{-1/3}L^{13/3}\). In particular \(Q(|\sigma|+|\theta|)=o(1)\), as required for (4).

By (2) and (9), uniformly for \(q\le h\le RH\),

\[
q\Psi(\sigma,\theta)
 \le\frac{q\eta}{\alpha}V_n(y)+Cn^{-1/3}L^{34}
 =\frac{q}{r}\left[\frac12\log r+\log\log r+c_*-d_n\right]
       +Cn^{-1/3}L^{34},
\quad r=h+\epsilon H.
\tag{25}
\]

This estimate does not extend legality: we only enlarge the upper bound from \(q\le h\) to \(q\le r\). On \(q>Q\), (1) gives
\(a(\sigma,\theta)=a_*+O(|\sigma|+|\theta|)\) and \(E_q=O(Q^{-1})\). Combining (4), (5), (24), and (25), the good-step row has mass at most

\[
m_*+2a_*e^{c_*-d_n}
 +O\!\left(\frac{\ell}{L}+L^{-2}
              +n^{-1/6}L^5+n^{-1/3}L^{110}\right).
\tag{26}
\]

All estimates are uniform in the source height and elapsed length. The head contributes its true critical mass only once. Since \(2a_*e^{c_*}=1-m_*\), (26) is

\[
1-(1-m_*)d_n+O(d_n^2)+o(d_n).
\tag{27}
\]

For completeness, the omitted steps have much smaller mass. The full transformed exponent is bounded by
\(C\eta L^{16}e+C\beta L^{16}|d|\).
For \(e>HL^{40}\), a fixed small extra positive length tilt in the common analytic neighborhood gives an upper bound

\[
\exp[-cHL^{40}+O(H)].
\]

For \(|d|>\sqrt H L^{40}\), splitting the two signs and adding \(\theta_0=cL^{40}/\sqrt H\) gives an upper bound

\[
\exp[-cL^{80}+C_Rc^2L^{80}+O(L^{57})].
\]

Choose \(c>0\) fixed and sufficiently small after \(R\); this is at most \(\exp[-c'L^{80}]\) for large \(n\). All cubic discriminant errors still tend to zero, since every relevant tilt is \(n^{-1/3}\) or \(n^{-2/3}\) times a fixed power of \(L\). These bounds use unrestricted destination sums and hence cover all omitted steps. They are \(o(d_n)\).

Consequently, for some fixed \(b_0>0\), every complete transformed row has mass at most

\[
1-b_0d_n,\qquad
\text{and one may take } b_0=(1-m_*)/2
\tag{28}
\]

for all sufficiently large \(n\). This establishes the required quantitative contraction rather than relying on a qualitative finite-height limit.

## 7. Terminal, renewal, and first-hit errors

The positive transformed Neumann sum is bounded by \((b_0d_n)^{-1}\). Its logarithm is \(O(\log L)=o(F/L)\).

The terminal representation is exactly the one in the audited positive macro-kernel: after elapsed macro-length \(k\), its factor is
\(\rho^{n-1-k}t^{1-h}\), apart from the fixed initial factor. Since \(g_n(1)=0\), (10) gives

\[
f_n(s,h/H)\le p_n(1)h/H+CL^{16}(1-s).
\]

Writing \(r_0=n-1-k\ge0\), the terminal product is bounded by a fixed constant times the exponential of

\[
r_0[\log\rho+O(\eta L^{16})]
+h[-\log t+\beta p_n(1)]+O(\eta L^{16}).
\]

The two small corrections tend to zero, while \(\log\rho<0\) and \(-\log t<0\). The terminal product is therefore uniformly bounded independently of \(n,k,h\). The initial-height adjustment is

\[
F[f_n(0,1/H)-f_n(0,0)]=\beta p_n(0)=o(1).
\]

Thus the confined coefficients satisfy

\[
a_n^{[\le RH]}\rho^n\le C_2d_n^{-1}e^{-Ff_n(0,0)+o(1)}.
\tag{29}
\]

The imported first-hit estimate is

\[
a_n^{[>RH]}\rho^n\le C_3\exp[-R^2F/(4D_0)]
\tag{30}
\]

for a fixed \(D_0>0\). Choose the fixed \(R\), in addition to the Legendre-domain requirement above, so that \(R^2/(4D_0)>C+1\). Equation (22) shows \(f_n(0,0)\to C\), so (30) is exponentially smaller than (29). Taking logarithms after adding the two positive contributions gives

\[
D_n\ge Ff_n(0,0)-O(\log L).
\tag{31}
\]

Combining (22) and (31) proves (T). More explicitly, this construction yields

\[
D_n\ge CF\left[1+\frac{7\ell}{3L}+\frac\kappa L\right]
 -2CF L^{-5/4}
 -O\!\left(F\frac{(1+\ell)^2}{L^2}+FL^{-4}+\log L\right).
\tag{32}
\]

Every error in (32) is \(o(F/L)\). No endpoint, terminal, or geometric-series term remains at the target scale.

## 8. What has and has not been established

This note closes the proposed one-sided argument at the exact \(F/L\) scale. It is logically independent of any new matching normalized-kernel lower construction, which requires its own proof and audit. The approved rectangle lower construction previously had an \(O(F/L)\) loss and cannot by itself turn (T) into a two-sided expansion.

Accordingly, the value \(\kappa\) is now justified as the next constant in this one-sided bound. Calling it the established next coefficient of the full deficit asymptotic still requires a matching upper bound on \(D_n\). The frozen approved second-order statements remain unchanged.
