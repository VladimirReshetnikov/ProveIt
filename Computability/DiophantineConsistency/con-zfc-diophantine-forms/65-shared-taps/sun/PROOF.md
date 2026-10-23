# Shared kernel taps with the ten-integer Sun finalizer

## Result and dependency boundary

`generated/sun10.json` specifies one fixed integer polynomial in the ten
unrestricted integer variables

    f,g,h,k,l,w,x,y,z,m.

Its exact total degree is **7,428,120**, and its division-free evaluator
has **525 binary arithmetic operations**: 337 multiplications, 161
additions, and 27 subtractions. All intermediate registers are polynomial
abbreviations, not extra unknowns. With the complete, authenticated old31
coefficient tuple included under `coefficients/`, ordinary mathematics
formalizable in ZFC proves

    no integer zero of F10  <=>  Con(ZFC).

The new result composes the compatible shared-tap source certificate with
the unchanged package59 Sun finalizer. The compiler/refutation calibration
and Sun's arithmetic bridge remain identified mathematical dependencies.
This is not a new end-to-end proof-assistant verification or a claim of
minimum possible variable count or degree.

The comparison is package59 at commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`: its ten-integer point has degree
8,469,528 and 533 operations. This adapter lowers degree by 12.2959% and
saves eight operations. The nine-positive equations elsewhere have a
different domain and are not ten-unrestricted-integer substitutes.

## 1. The fixed source certificate

Use the original, unshifted 65-gate 31-positive-coordinate source in
`data/source_system65.json`. Its four fixed ports have bit lengths
`(1064921,1070004,1064921,1064922)` and the fourth is already shifted
`MF_source`. All four ports are bound together. Replace row 14 by row 14
plus row 2, and row 15 by row 15 plus row 3.

The primary layout and the three coalesced kernels are exactly
`data/layout.json` and `data/kernels.json`. Equal coefficient requirements
at one kernel position are inserted **once**, not added once per owner.
The shared-tap theorem and proof are reproduced in
`inherited/shared_taps_proof.md`, Sections 1--2. The independent checker
expands the 65-gate source and verifies all

    22*(1+31+496)=11,616

target/monomial coefficient requirements, including every absent monomial.
It proves

    [Z^q_j] (D2(Z) U_p(Z)^2+D1(Z) U_p(Z)+D0(Z)) = 2 rho_j(p),
    U_p(Z)=sum_i p_i Z^w_i.

The 89 weighted source records use 84 distinct kernel taps. The numerical
parameters are

    W=max_i w_i=116, Q=max_j q_j=1841,
    (deg D0,deg D1,deg D2)=(1384,1739,1641),
    H=max_d(deg Dd+dW)=1873.

The highest coefficient of D2 is +1. If `C0=2^2134927`, every kernel
coefficient has absolute value strictly below C0. Take

    kappa=2134940, betaS=2^kappa.

This deliberately even kappa satisfies `betaS>4096 C0` and preserves the
Sun source congruence modulo 3.

## 2. New source polynomials

In the unrestricted integer variables f,g, put

    b=1+3f, B=betaS b^2, ell=sum_i B^w_i, Uc=ell+g,
    Gc=D2(B)Uc^2+D1(B)Uc+D0(B), AT=sum_j B^q_j,
    N0=B^117, N1=B^1874, N=N0 N1=B^1991,
    M0=N0-1-(b-1)ell,
    Jc=2Gc+AT, Sc=g+Jc N0, Tc=M0+(B-2)AT N0,
    X=N^2+(Sc+Tc)N+N-1-Sc,
    Y=betaS^15 * 2^(kappa-21) * B^2114 * b,
    cap=b B^116.

Equivalently `Y=2^(2130 kappa-21) b^4229`. These expressions are integer
polynomials; every exponent is a fixed nonnegative integer. Their exact
degrees in f,g are

    deg X=7964, deg Y=4229, deg cap=233.

The new kernel source needs no positive padding at a higher base position.
Its sign bootstrap is explained in Section 5 below and must precede the
following source bounds.

## 3. Pre-binary positivity and the strict block range

Assume b is a square, f is nonzero, and `0<g<2 cap`. Since
`b=1 mod 3`, this gives `b>=4` and `B>4096 C0 b^2`. The distinct positive
weights imply

    B^116 <= Uc < 3b B^116.

The three kernel estimates are

    D2(B) > B^1641/2,
    |D1(B)| < 2 C0 B^1739,
    |D0(B)| < 2 C0 B^1384.

After division by `B^1641 Uc^2`, the possible negative contributions are
bounded by `2 C0/B^18` and `2 C0/B^489`. Each is below 1/8. Therefore

    Gc > B^1641 Uc^2/4 > 0.

For the upper bound,

    |Gc| < 2 C0(1+3b+9b^2)B^1873 <= 26 C0 b^2 B^1873,
    2Gc < N1/64.

Both AT and `(B-2)AT` are less than `N1/64`, since the target ceiling is
32 base positions below H. Hence

    0<Jc<N1/32, Jc+(B-2)AT+2<N1.

The ordinary base-B digits of M0 are B-1 except for digits B-b in the
31 coordinate positions. Thus `0<=M0<N0`, and also `0<g<N0`. Combining
these bounds gives the essential strict range

    0<=Sc, 0<=Tc, Sc+Tc<N.

It follows that `X>=N^2>3b` and `Y>max(b,256)`. The even kappa gives
`B=N=1 mod 3`, and therefore `Tc=-22 mod 3` and `X=0 mod 3`.
All of these assertions precede recovery that b is a power of two.

## 4. Bit extraction and the exact population threshold

Once b is a power of two, so are B,N0,N. The low mask condition
`g & M0 = 0` says exactly

    g=sum_i n_i B^w_i, 0<=n_i<b.

The polynomial Uc then encodes positive source coordinates `p_i=n_i+1`.
If `hs=[Z^s]G_p(Z)`, every coefficient, including unmarked overlaps,
satisfies

    |hs| < C0[(sum_i p_i)^2+sum_i p_i+1]
         <= 993 C0 b^2 < B/4.

The signed coefficient of Jc at s is `2hs+epsilon_s`, where epsilon is
one at a target and zero otherwise. Normalization into base-B digits has
incoming carries only -1 or 0. At a target, the mask B-2 admits precisely
digits 0 and 1. The padded coefficient passes this mask precisely when
hs=0, regardless of the incoming carry. Thus

    Sc & Tc = 0
    <=> g encodes n_i in [0,b) and all rho_j(n+1)=0.

The already-proved positivity of Jc is needed here; signed coefficients
alone would not justify speaking of its ordinary digits.

For `N=2^u` and `S,T>=0` with `S+T<N`, the polynomial
`X*=N^2+(S+T)N+N-1-S` satisfies

    s2(X*)=1+u+s2(T)-[s2(S)+s2(T)-s2(S+T)].

The bracket is nonnegative and vanishes precisely for `S & T=0`.
Legendre's formula gives `v2(binomial(2X*,X*))=s2(X*)`. Here, writing
`b=2^k` and `B=2^v`, the actual mask population is

    s2(Tc)=139v-31k-22, u=1991v,
    1+u+s2(Tc)=2130v-31k-21=log2(Y).

Consequently the required binomial divisibility is equivalent to all the
positive source equations.

Conversely, a positive source zero cannot be the all-one vector, since
row five has value 1 there independently of the fixed ports. Choose
arbitrarily large `b=4^s` exceeding every source coordinate and encode
`n_i=p_i-1`. Then `B<=g<cap`, all target masks pass, and the required
binomial divisibility holds. This supplies the forward source contract
with its lower bound on g as well as the reverse source contract.

## 5. The unchanged finalizer and its sign order

The full explicit formulas are in `tail.py`; they are also written in
`inherited/package59_section.tex`, under “Explicit radical-free finalizer.”
`verify.py` checks that this function is syntax-tree identical to the
pinned package59 function. Only its polynomial arguments b,X,Y,cap change.

For clarity, its decisive ingredients are

    L=lY, U=2LX, V=4gwY, W=bw,
    A=U(V+1), Bstar=2X+1, C=Bstar+(A-2)h,
    P=U^2V, K=X+1+k(P-2),
    Sstar=2A-5, Tstar=3WC-2(W^2-1),
    R2=(P^2-4)K^2+4,
    Delta=8 cap^3 g K^2-g^2[32(C-KL)^2 cap^3+g^2 K^2],
    O=f^2 l^2 Delta, xi=zx,
    a0=b[1+(3O-4)b^2z^2].

The remaining Lucas expressions D,F,I are the identical fixed polynomials
in the inherited finalizer. Set `a1=R2`, `a2=DFI`,

    w0=1, w1=a0, w2=a0(P^2+K^2+3),
    r=Tstar+Sstar y,
    Sigma=xi Sstar^5,
    Theta=(r^3-r Sstar^2-Sstar^3)(r^2+23 Sstar^2),
    Z=Sigma m-Theta, Ai=Sigma^2 wi^2 ai,
    Vn=Z^2+A2-A0-A1,
    Wn=Vn^2+4Z^2 A2-4A0 A1,
    F10=Wn^2-16Vn^2 Z^2 A2.

The finalizer's norm/separation argument first proves from `F10=0` that
`Sigma!=0`, all three ai are integer squares, and `Sigma | Theta`.
In particular z is nonzero. This part uses only integer polynomial
identities, the intersective quintic, and the structural separator; it
does not use positivity of Gc.

The two factors of a0 are coprime. Since their product is a square,
both are signed squares of the same sign. The congruence `b=1 mod 3`
excludes a negative square, so b is a positive square. The case b=1 would
give f=O=0 and `a0=1-4z^2<0`, which is impossible. Thus b>=4 and f!=0.
The second factor being a nonnegative square also forces O>0: if O<=0
it is at most `1-4b^2z^2<0`.

Now `O=f^2 l^2 Delta>0` gives Delta>0. Since cap is positive, the displayed
formula for Delta rules out g<=0 and K=0. Dividing its strict positivity
by `g K^2>0` gives

    g^3<8 cap^3, hence 0<g<2 cap.

This proves precisely the hypotheses used in Section 3. There is no
circularity between source positivity and the signed-input finalizer, and
no all-real positive padding term is required.

The unchanged Sun bridge then recovers b a power of two and the binomial
divisibility, so Section 4 produces a positive source zero. Conversely,
Section 4's cofinal forward source witnesses meet the unchanged bridge's
hypotheses. Its Pell witnesses, residue interpolation, and norm merger
give an integer zero of F10. Composing with the inherited 31-coordinate
compiler theorem proves the stated consistency equivalence.

The specific primary arithmetic dependencies are Z.-W. Sun, *Further
results on Hilbert's Tenth Problem*, Science China Mathematics 64 (2021),
281--306, Theorems 4.12--4.13, and *Ten unknowns for Hilbert's tenth problem
over the integers*, 2026 preprint, Propositions 6.1--6.2:

https://arxiv.org/html/1704.03504v7

https://arxiv.org/html/2609.01594v2

## 6. Exact degree and replay

The complete fixed-port payload hashes are verified before the degree
certificate is evaluated. Propagating the source degrees through the
literal finalizer gives

    456*7964+896*4229+24*233+1760 = 7,428,120.

There is also a positive analytic leading-coefficient certificate. Under
the diagonal specialization of all ten variables to t, write the leading
coefficients of X,Y,cap as x0,y0,c0. The source formulas give

    x0=3^7964 betaS^3982,
    y0=3^4229 betaS^2129 beta_mask,
    c0=3^233 betaS^116,  beta_mask=2^(kappa-21).

The scaled radicand A2 has degree 1,857,030 and leading coefficient

    2^362 * 3^8 * x0^114 * y0^224 * c0^6.

It is the unique dominant term in Vn. Thus Wn has degree 3,714,060 and
leading term A2^2. The subtracted term `16 Vn^2 Z^2 A2` has degree
5,735,370, below twice the degree of Wn. The leading term of F10 is
therefore A2^4, with diagonal coefficient

    2^1448 * 3^32 * x0^456 * y0^896 * c0^24
      = 2^(3727056 kappa-17368) * 3^7426392 > 0.

This proves the matching lower bound directly and does not require an
assumption about any large source-coefficient residue.

After all ten variables are specialized to a common indeterminate t,
the coefficient of that degree has residues

    95 mod 101, 646 mod 1009, 515853 mod 1000003.

The verifier checks these against the analytic expression as well. Any one
nonzero residue is a second certificate of the matching lower bound; this
is a leading-coefficient computation, not testing random values of the
equation. The exact source proof and local circuit identities are
independent of the modular degree calculation.

Run `python build.py` and `python verify.py` from this directory, or pass
their paths from another working directory. Verification checks 11,616
source coefficients, 59 local identities, the Lucas factorization, the
eight-factor norm identity, all fixed-port hashes, and the final degree.
A deliberately corrupted shared tap is rejected. Supplemental finite
checks cover 476 borrow transitions, 11,049 binary block pairs, and 44
exact source assignments including nonbinary square bases 25 and 49.
These finite checks support the implementation; the unbounded mathematical
argument above and its identified inherited theorems prove the equivalence.
