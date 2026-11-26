# Independent referee report: sharp exact aggregate torsion selection

**Verdict:** I find the proposed scalar theorem and the integral bounded-series,
multivariate, and aggregate-packet extensions mathematically correct. The
linear endpoint in the valuation budget, including its floor and strict
integer-threshold behavior, survives independent checking. The construction
attaining the obstruction budget is valid over a finite cyclotomic extension.
This is a mathematical proof review, not a Lean/kernel verification or a
certification of literature novelty.

The reviewed draft is
`research/prior_reports/aggregate_minimax_referee.tex`.

## 1. Exact statement checked

Let p be prime, let v(p)=1 on C_p, let

    e_h=(p-1)p^(h-1),  r_h=1/e_h,
    Z_h={zeta-1 : zeta has exact order p^h}.

Take h_0>=1 and a finite real rho>=r_{h_0}, and put c=p^(1-h_0).
For nonzero g in C_p[T], define

    G_u(g)=min_j(v(a_j)+ju),  Delta_rho(g)=G_rho(g)-G_0(g).

For H>=h_0 the least possible Delta_rho(g) under the requirement

    v(g(z))>G_rho(g) for every z in every Z_h, h_0<=h<=H,

is exactly (H-h_0+1)c. Consequently the scalar endpoint

    H=h_0+floor(Delta_rho(g)/c)

always contains a good point with v(g(z))<=G_rho(g). For integral g,
G_0(g)>=0, so the stated sufficient endpoint

    H=h_0+floor(B*p^(h_0-1))

follows from G_rho(g)<=B. The budget B should be explicitly finite and
nonnegative in the integral formulation. These conditions are automatic
if it bounds the finite Gauss valuation of a nonzero integral series.

## 2. Arbitrary C_p roots really reduce to marked torsion points

This is the first place an exact extremal claim could have failed, but it
does not. Given a same-shell root alpha, choose w in Z_h maximizing
v(w-alpha). Then for every z in Z_h,

    v(z-w)>=min(v(z-alpha),v(w-alpha))=v(z-alpha).

Thus moving alpha to its nearest torsion endpoint can only increase its
potential everywhere on that shell. The endpoint may be repeated; no
Galois invariance or distinct-root condition is needed. A root already at
an endpoint is handled by v(0)=infinity.

For m<e_h marks, choose a least-occupied unit class modulo p, then a
least-occupied child modulo each successive power of p. At depth j its
occupancy is at most floor(m/e_j), including zero at depth h. The selected
endpoint is therefore unmarked and has finite potential. The exact
distance formula gives

    sum_i (v(z-alpha_i)-r_h)
      <= U_h(m)=(1/e_h)*sum_{j=1}^{h-1} e_j*floor(m/e_j).

The formula also covers h=1, where the sum is empty. For p=2, the first
branch has one class, and the same argument still works.

The bound is sharp for every m<e_h: mark the first m positive unit
exponents. Every unit residue class modulo p^j then has at least
floor(m/e_j) marks. Hence every unmarked endpoint has potential at least
U_h(m), while the least-occupied-branch argument supplies one at most
U_h(m). This is an exact maximin identity, not merely a convenient bound.

## 3. Off-shell roots cannot subsidize an obstruction

Factor g=b product_alpha(T-alpha). The Gauss identity is

    G_u(g)=v(b)+sum_alpha min(u,v(alpha)).

All contributions to Delta_rho are nonnegative. A root of valuation
r_h<=rho contributes exactly r_h to Delta_rho. Roots of negative
valuation contribute zero, roots at zero contribute rho, and neither
case causes an exception.

At a test point z in Z_h, all off-shell root contributions are exact by
strict ultrametricity. Therefore

    v(g(z))-G_rho(g)
       = E_h(z) - [G_rho(g)-G_{r_h}(g)],

where E_h uses only roots on shell h. If m_k is the count on shell k,
the bracket is at least

    sum_{k=h_0}^{h-1} (r_k-r_h)m_k.

Additional roots above, below, or between the selected shells never
decrease this slack. This confirms that arbitrary nonintegral
coefficients and arbitrary root radii do not defeat the proposed lower
bound.

## 4. The integer threshold and induction are exact

Write n=h-h_0 and M_h=(p-1)p^n=e_{n+1}. Assuming all earlier shells are
blocked, the inductive counts m_k>=M_k force slack at least

    S_h=n*c-(p^n-1)/e_h.

Direct computation gives

    U_h(M_h-1)=S_h.

For h_0=1, M_h=e_h. In the convenient sum through j=n+1=h, the extra
j=h summand is zero, so no missing endpoint term occurs. For n=0 both
sides are zero, which proves the base case. If m_h<M_h, an endpoint has
E_h(z)<=U_h(m_h)<=S_h, contradicting the required strict inequality.
Hence m_h>=M_h and its budget cost is at least

    m_h*r_h>=M_h/e_h=c.

Blocking N shells consequently costs at least Nc. Taking
N=floor(B/c)+1 yields Nc>B even when B/c is an integer. The exact
comparison is essential: replacing N by floor(B/c) would be false at
integer budgets.

## 5. Sharpness construction and strict margin

For each h=h_0,...,H, choose the M_h roots

    zeta_{p^h}^a-1,  1<=a<=p^(h-h_0+1),  p does not divide a,

and multiply the corresponding linear factors into a monic polynomial g.
The roots are distinct within each shell. Its coefficients are integral,
G_0(g)=0, and G_rho(g)=Nc, where N=H-h_0+1. Its degree is

    sum_{n=0}^{N-1}(p-1)p^n=p^N-1.

For h_0=1, this uses every endpoint in every selected shell and hence
vanishes at all of them. For h_0>=2, the occupancy construction gives
minimum on-shell excess

    U_h(M_h)=(n+1)c.

Its difference from the earlier-shell slack is

    U_h(M_h)-S_h=(p^(n+1)-1)/e_h>0.

Thus every endpoint fails strictly, including unmarked endpoints; this
checks the strongest requirement in the proposed sharpness claim.
The construction may need a coefficient field containing p^H-th roots of
unity. It proves the stated uniform sharpness over C_p and finite
extensions, not necessarily sharpness when coefficients are restricted
to Q_p itself.

## 6. Multivariate induction is sound

For an integral polynomial F, choose a coefficient polynomial f_beta(T_1)
such that

    G_rho(f_beta)+rho*|beta|=G_rho(F).

The scalar theorem selects z_1 with
v(f_beta(z_1))<=G_rho(f_beta), using the same budget B because
0<=G_rho(f_beta)<=G_rho(F)<=B. The specialized polynomial is nonzero,
integral, and has Gauss valuation at most G_rho(F). Iterate.

There is no hidden dimension dependence in this argument. It does **not**
assert that all chosen coordinates have the same exact torsion order;
their orders can differ within the common interval. Forcing equal orders
would be a different theorem and is not proved here.

## 7. Bounded series and the nonattained G_0 issue

An integral formal power series in finitely many variables converges at
every point of the proposed finite torsion grid because every coordinate
has valuation at least r_H>0. Choose a total degree D with

    (D+1)r_H>B.

Since r_H<=rho, the degree-D truncation has the same G_rho as the series,
and the omitted tail has valuation>B uniformly throughout the grid. A
good point for the truncation is consequently good for the series, with
the same value by strict ultrametricity. No limiting choice of points or
compactness assertion is needed.

The optional sharper statement for nonintegral bounded series also
works. Put

    a=inf_nu v(a_nu)>-infinity,  M=G_rho(F),  Delta=M-a.

The infimum need not be attained and need not belong to the value group.
One should **not** justify the result by multiplying by a scalar of
valuation -a. Instead retain a as a real uniform lower bound. Every
specialization at integral torsion points has coefficient valuations at
least a; the chosen coefficient makes its new Gauss valuation at most
M. A selected coefficient polynomial has its own Delta at most M-a.
The common budget therefore remains Delta during the induction.

For a series, choose D with a+(D+1)r_H>M. Its truncation has G_rho=M and
G_0>=a, so its polynomial budget is at most Delta; the tail argument is
unchanged. This proves the sharper bounded-series extension without any
assumption that G_0 is a minimum.

## 8. Packets mean aggregate control only

For a finite packet, Gauss multiplicativity gives

    G_rho(product_i F_i)=sum_i G_rho(F_i).

Applying the theorem to the product yields one common tuple with

    sum_i v(F_i(z))<=sum_i G_rho(F_i).

Separate witness points of coordinate valuations at least rho bound each
G_rho(F_i), as claimed. The conclusion does not imply any individual
inequality v(F_i(z))<=G_rho(F_i); some factors can lose while others save.
The draft states this distinction correctly. For nonintegral packets it
is enough to use the lower coefficient bound sum_i inf v(coeff F_i);
no extra normalization is required.

## 9. Independent finite verification

`verify_shell_minimax_exhaustive.py` exhausts **every** marked multiset
with m<e_h for seven small shells: (p,h)=(2,1),(2,2),(2,3),(2,4),
(3,1),(3,2),(5,1). It computes the actual best minimum potential and
compares it with U_h(m), using exact scaled integer distances.
All 27 budget cases pass. The output `exact_referee_checks.json` records
the shell-by-shell counts and maxima. This is an independent extremal
enumeration, distinct from checking only the balanced construction or
the algebraic floor identity. It supports, but does not replace, the
argument above.

## 10. Recommended final presentation

State the obstruction-cost theorem first, then the endpoint corollary;
this makes both the floor and the sharpness transparent. Present the
integral multivariate-series theorem as the main application and the
Delta variant as an explicit strengthening. Label the packet result as
aggregate. Record that novelty relative to the previous ProveIt reports
has been checked, while novelty in the broader literature is not
certified. Do not label the proof Lean-verified unless a corresponding
formal implementation has actually been compiled and checked.

## 11. Follow-up: Lubin--Tate extension (validated)

**Verdict:** the same sharp theorem holds for a one-dimensional
Lubin--Tate formal O_K-module, with p replaced by the residue cardinality
q, provided the valuation is normalized by w(pi)=1. No extra ramification
factor belongs in this normalization.

### Primary references

Jonathan Lubin and John Tate, *Formal Complex Multiplication in Local
Fields*, Annals of Mathematics (2) **81** (1965), 380--387,
DOI: <https://doi.org/10.2307/1970622>.
Accessible scan:
<https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/lubin-tate.pdf>.
Theorem 1 on pp. 382--383 constructs the integral formal O_K-action;
Theorem 2(b), p. 383, identifies the pi^h-torsion module with
O_K/pi^h O_K. The proof of Theorem 2 starts on p. 384 and uses the
standard series pi T+T^q after an integral strict isomorphism.

For related analytic applications, see Vlad Serban, *An infinitesimal
p-adic multiplicative Manin--Mumford Conjecture*, Journal de Theorie des
Nombres de Bordeaux **30** (2018), 393--408, Section 3 and Theorem 3.7,
DOI: <https://doi.org/10.5802/jtnb.1030>, full article:
<https://www.numdam.org/item/JTNB_2018__30_2_393_0.pdf>.
That paper supplies context, not the exact budget theorem proved here.
Use the normalization below explicitly: with v_p(p)=1 and K ramification
index e_K, one has w=e_K v_p. Thus a primitive point has v_p-valuation
1/[e_K(q-1)q^(h-1)].

### Primitive radius: a direct proof for general Lubin--Tate series

Let F be the formal group and f(T)=[pi]_F(T). By definition

    f(T)=pi T+sum_{i>=2} a_i T^i,
    f(T) congruent to T^q modulo pi.

Thus a_q is a unit, and every a_i for i!=q is divisible by pi. At a
nonzero point t of positive valuation s, the only candidates for the
least term valuation in f(t) are 1+s and q*s. Every other term is
strictly larger than the smaller of these.

If t is nonzero pi-torsion, f(t)=0 forces 1+s=q*s, hence
s=1/(q-1). If t has exact level h>=2, f(t) has exact level h-1.
Inductively its valuation r_{h-1} is at most r_1. The case s>=r_1
would give w(f(t))>=q/(q-1)>r_1, impossible. Hence s<r_1, the
q-th term is the unique least term, and w(f(t))=q*s. This gives

    w(t)=r_h=1/((q-1)q^(h-1)).

This proof avoids treating a general infinite Lubin--Tate series as a
polynomial or assuming an unproved polynomial quotient is Eisenstein.
The standard torsion-module theorem gives exactly
e_h=(q-1)q^(h-1) primitive points.

### Ordinary difference equals formal difference in valuation

Let i_F(Y)=[-1]_F(Y). The integral series
F(X,i_F(Y)) vanishes after X=Y, and its linear term is X-Y.
Consequently

    F(X,i_F(Y))=(X-Y) U(X,Y),
    U in O_K[[X,Y]], U(0,0)=1.

For x,y of positive valuation, the evaluated U(x,y) is a unit. Hence

    w(x-y)=w(F(x,i_F(y))).

Choose a generator t_h of F[pi^h]. The primitive points are [a]_F(t_h)
for units a modulo pi^h. If a!=b modulo pi^h and
j=v_pi(a-b)<h, the formal difference is [a-b]_F(t_h), which has
exact level h-j. Therefore

    w([a]_F(t_h)-[b]_F(t_h))=r_{h-j}.

This proves the exact ordinary metric required for the polynomial root
factorization argument; substituting formal subtraction without the unit
factor would have left an actual gap.

### The same extremal tree and conclusion

Unit classes have q-1 branches at the first residue level and q branches
at every subsequent level. The previous counting argument therefore gives

    U_h(m)=(1/e_h) sum_{j=1}^{h-1}e_j floor(m/e_j),
    e_j=(q-1)q^(j-1),

without change. For h_0>=1, rho>=r_{h_0}, c=q^(1-h_0), blocking N
consecutive primitive levels costs exactly N*c in Delta_rho. Thus an
integral nonzero ordinary polynomial or bounded multivariate power series
with G_rho<=B has a primitive Lubin--Tate torsion tuple, with each
coordinate's exact level in

    [h_0, h_0+floor(q^(h_0-1) B)],

at which its valuation is at most G_rho. The optional Delta_rho budget
and the aggregate packet formulation transfer as well.

For sharpness, at shell h let L=h-h_0+1. Choose exactly one unit lift
modulo pi^h of every unit class modulo pi^L, and use the corresponding
M_h=e_L points as ordinary polynomial roots. At every depth j<=L the
occupancy is exactly M_h/e_j. Thus the same strict slack calculation
applies, with q replacing p. The product over N shells has degree
q^N-1, integral coefficients in a finite division field, and budget
N*q^(1-h_0). This establishes the claimed exactness.
