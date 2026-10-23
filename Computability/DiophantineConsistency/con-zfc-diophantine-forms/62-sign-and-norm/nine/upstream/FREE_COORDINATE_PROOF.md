# Free-coordinate composition with the degree-separated source

## Result and provenance

This is a separate, newly composed equation, not an edit to the frozen
`nine/` family. Its primary literal circuit is
`generated/split_116_positive.json` on nine strictly positive integers

    b, g, h, s, w, C, i, j, n.

Its exact total degree is **1,910,404** and its live binary circuit has
**473 operations**: 162 additions, 22 subtractions, 289 multiplications.
All powers have fixed integer exponents, every fixed leaf is an ordinary
specified integer coefficient, and intermediate registers add no unknowns.

The late supplied FreeCoordinate contribution provides two credited ideas:
making the carrier C free with a quotient shift, and removing the leading
binary block while reducing the threshold. Its original proof and independent
review are retained verbatim as `upstream/free_coordinate_PROOF.md` and
`upstream/free_coordinate_REVIEW.md`; their source is the supplied archive
at repository snapshot 4b4349064a750ba6347293b55874a7f92abdd0db. Raw-file
hashes and original archive paths are in `SOURCE_PINS.json`. The new builder
does not execute upstream programs. The present work combines those ideas with the new
split116 source and the already reviewed normalized-margin finalizer.

The semantic conclusion is unchanged: ZFC proves existence of a positive
zero equivalent to a finite syntactic ZFC refutation. Negating this gives
absence of positive zeros iff Con(ZFC). The inherited original31 compiler
and numerical Jones ratio theorems remain explicit premises. This is not a
consistency proof, a new end-to-end kernel formalization, or a minimum claim.

## 1. Source and fixed coefficients are unchanged

Use `data/parent_source.json`, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`, together with the
complete original31 four-port tuple in `coefficients/old_tuple`. The four
unsigned little-endian payloads are authenticated together. Their bit lengths
are 1064921,1070004,1064921,1064922, and MF is already shifted. No port from
the newer native tuple is substituted. The complete coefficient/compiler
adapter is `upstream/old_tuple_complete_proof.md`.

The source row operations are rho14=r14+r2 and rho15=r15+r3, with all other
rows unchanged. Their inverses preserve the entire positive common zero set.
The unchanged split certificate and kernels have 89 weighted records,
31 positive positions of maximum W=116, and 22 targets of maximum 2129.
The three kernel degrees are 1719,2027,1929, and D2 has leading coefficient 1.
Their convolution height is 2161. The checker exhaustively verifies the
22,544 same-degree isolation interactions and the exact weighted kernel data.

For U_y(T)=sum_i y_i T^w_i and the three reversed kernels, the exact identity is

    [T^q_j](D2(T)U_y(T)^2+D1(T)U_y(T)+D0(T))=2rho_j(y).

Weighted coefficients have absolute value below M=2^2134927. Retain

    kappa=2134939, a=2^kappa=4096M, B=ab^2,
    ell=sum_i B^w_i, Us=ell+g,
    Gs=(D2(B)Us+D1(B))Us+D0(B),
    Targets=sum_j B^q_j,
    N0=B^117, Z=B^2162,
    Mask=N0-1-(b-1)ell,
    Jcode=2Gs+Targets,
    Scode=g+N0 Jcode,
    Tcode=Mask+N0(B-2)Targets,
    Gcap=32bB^116.

For every b,g>=1, Us>=B^116, D2(B)>B^1929/2,
|D1(B)|<2MB^2027 and |D0(B)|<2MB^1719. Relative to
B^1929 Us^2 the negative terms are below 2M/B^18 and 2M/B^442, each
below 1/8. Thus Gs>0 and Scode,Tcode>=0 before any final-zero or binary-base
assumption. The low mask lies in [0,N0).

On the exact ratio-derived branch g<4bB^116, we have Us<6bB^116, and

    2Gs/Z < 86Mb^2/(B-1) < 1/32,
    Targets < Z/64,    (B-2)Targets < Z/64.

The second strict inequality uses B=4096Mb^2 and B>=4. Since g<N0 and
Z>128, these bounds give

    Scode+Tcode < N0 Z = B^2279.

In particular, this proof does not silently use the weaker range g<2bB^116.

When b is a power of two, the low mask recovers
g=sum z_iB^w_i with 0<=z_i<b. The word Us then encodes y_i=z_i+1>0.
Every coefficient h_t of the split convolution satisfies
|h_t|<993Mb^2<B/4. The unchanged sparse +1 borrow proof therefore gives

    Scode & Tcode=0 iff g encodes a positive common source zero.

Conversely a source zero gives g>0, because the all-one source tuple has
r5=1. Every sufficiently large power-of-two b is allowed, and
g<bB^116, hence 32g<Gcap. Complete source details remain in the frozen
proof retained as `upstream/frozen_nine_PROOF.md`; all the required source
inequalities are restated here for the new composition.

## 2. Remove the leading block and recalibrate exactly

Replace the old outer registers by

    L=bB^2279,
    R=L(Scode+Tcode+1)-Scode-1,
    c=2^17079501, N=cbB^1201.

For every outer assignment,
R=(L-1)Scode+LTcode+L-1>=L-1>=8; also b<=R,N and N>=8.
Thus the unconditional Jones numerical hypotheses remain valid.
On the bounded branch, Scode+Tcode<B^2279<=L, strictly, even for b=1.

If b=2^k and B=2^v, write L=2^u. The two nonoverlapping blocks of

    R=(Scode+Tcode)L+(L-1-Scode)

give

    pop(R)=u+pop(Tcode)-tau,
    tau=pop(Scode)+pop(Tcode)-pop(Scode+Tcode)>=0.

The defect tau is zero precisely for binary-disjoint Scode,Tcode. The mask
population is unchanged: pop(Tcode)=139v-31k-22, while u=k+2279v.
Hence the exact threshold is

    u+pop(Tcode)=2418v-30k-22
               =2(17079501+k+1201v)=2log_2 N,

because v=kappa+2k and 16kappa-22=2*17079501. Legendre's valuation formula
therefore proves

    N^2 | binomial(2R,R) iff Scode & Tcode=0.

The calibration includes b=1 (k=0); it does not impose an artificial
restriction on powers of two. In fact b=1 cannot yield a final zero: its low
mask is N0-1, and 0<g<4B^116<N0 gives g & Mask=g>0. This is a changed
polynomial with a newly calibrated threshold, not an informal deletion from
the old polynomial.

## 3. Free C, exact CRT transport, and the quotient shift

All input coordinates are now positive. In the formulas below use
j0=j-1>=0. Define the unchanged ratio registers except for free C and H:

    U=N^2w, Y=N^2s, M0=RY,
    P=2M0^2U, K=R+1+h(P-1), A=M0(U+1),
    B1=2R+1, W1=bw,
    J=4A-5, Q=3W1C-2(W1^2-1),
    D=(A^2-1)C^2+1, k0=iJC, E=k0DC,
    F=(A^2-1)E^2+1,
    G=A+F(CD+1-A),
    H=C+F(B1+j0 C),
    I=(G^2-1)H^2+1,
    a0=(P^2-1)K^2+1, a1=DFI,
    t=bB^116, m=K^2(4t-g)-16t(C-KY)^2.

The normalized margin satisfies

    8m=[K^2-4(C-KY)^2]Gcap-8gK^2.

Its strict sign is exactly the old margin's sign. The CRT coordinate still
uses j0=j-1; replacing it by unshifted positive j would require an unsupported
cofinality assumption and is not done.

Even for C=1, all radicands and majorants below are positive. We have A>=2,
J>=3, D>=A^2, D>C^2, F>=A^2, G>A, H>1. Also A>W1, since b<=N and
A>U=N^2w>=bw. The only former unconditional inequality lost is Q>0.
The quotient shift repairs it exactly:

    E0=J(n+W1^2)+Q
      =Jn+(J-2)W1^2+3W1C+2 > 0.

If m>0, then |C-KY|<K/2. Since Y>=64,

    C>K(Y-1/2)>2K>=2(P+R)>2R+1+W1.

Here K>=P+R and P>U>=W1. Thus phi=C-B1-W1 is a positive integer,
recovering the old carrier range without assuming it in advance.

The exact CRT substitution is preserved because F=1 modulo both J and C.
From an old divisible witness H_old=B1+j_old C, j_old>=1, its positive
quotient (H_old-C)/F is B1 modulo C. With the old carrier range B1<C it
is uniquely B1+j0 C for j0>=0. Conversely the present H is the old one for

    j_old=1+((F-1)/C)B1+Fj0>=1.

Therefore, once m>0 has recovered the carrier range, the exact ratio
conditions are a0 square, a1 square, J|Q, m>0. Jones soundness returns
b a power of two, 8g<Gcap and the binomial divisibility; completeness uses
the already established 32g<Gcap source bound.

## 4. Positivity-first norm remains valid for free C

Define positive polynomial majorants

    V0=PK, Tpair=k0(8D^2-4D-1), V1=Tpair GH.

Their unchanged identities are

    V0^2-a0=K^2-1>0,
    Tpair^2-64DF=(8D+1)k0^2-64D>0,
    Delta1=V1^2-64a1
      =[(8D+1)k0^2-64D](GH)^2+64DF(H^2-1)>0.

They require only C>=1 and k0>=3, not the old carrier bound. Put

    Omega=Jm,
    Theta=E0-Omega(V0+V1),
    F9=[Theta^2-Omega^2(a0+64a1)]^2-256Omega^4 a0a1.

If m=0, then F9=E0^4>0. Otherwise a zero gives real signed roots
r0^2=a0, r1^2=64a1 and the factor identity

    n+W1^2+Q/J=m(V0+V1+r0+r1).

Its left side is positive by E0>0; its right-hand parenthesis is positive
by the unconditional strict majorants. Thus m>0 follows before any
integrality assertion. Recover the old carrier range as above. Then
A^2>P, D>C^2, F>=A^2, G>=A, I>=G^2 and C>K imply

    a1=DFI>C^2A^4>K^2P^2>a0.

The rational sum x=r0+r1=Theta/Omega is nonzero, and
2xr0=x^2+a0-64a1 makes both roots rational and hence integral. The
rational square root r1/8 of a1 is integral as well. Now the factor identity
gives J|Q, so all Jones conditions hold. This proves soundness.

For completeness, take the ratio witnesses, retain their positive C and
transform j_old exactly. Choose positive integer roots. Since A>W1 and
D>=A^2, D>C^2, we have W1^2<D and W1C<D. Also
Q/J<=W1C, so

    W1^2+Q/J < 2D < V1.

The latter follows from Tpair>=9D and G,H>=1. Since the actual normalized
integer margin m>=1, the choice

    n=m(V0+V1+r0+r1)-W1^2-Q/J

is an integer strictly greater than 0. It makes one factor vanish. This
proves completeness with the stipulated strictly positive n; n is not
arbitrarily shifted while holding an old norm witness fixed.

## 5. Exact degree and arithmetic audit

The source's diagonal heads are deg(Scode)=4556, leading coefficient
2a^2278; deg(Tcode)=4494; deg(L)=4559, leading coefficient a^2279.
Therefore R has exact degree r=9115 and head 2a^4557. N has degree
q=2403 and head ca^1201. In particular, omitting the old L^2 changes
the leading source term and is reflected in the certificate.

The separate degree circuit resolves the final cancellation by the exact
identity

    Theta^2-Omega^2(a0+64a1)
      =E0^2-2E0 Omega(V0+V1)
       +Omega^2[(K^2-1)+Delta1+2V0V1].

Decisive degrees are

    A 18729; D 37460; k0 18731; F 149842; G 187303; H 158957;
    a0 130606; a1 879822; m 75151; Omega 93880;
    V0 65303; V1 439911; Delta1 767442.

The term Omega^2 Delta1 uniquely dominates the inner polynomial, of degree
955202. Its square dominates the final subtracted norm term of degree 1385948.
Thus

    deg F9=104r+400q+8W+316=1,910,404,
    diagonal leading coefficient=2^186 a^954792 c^400>0.

The diagonal attains the multivariate upper bound, proving exactness for
the actual coefficient tuple. The main and certificate circuits use equal
polynomials; the supplied checker proves the needed identities and modularly
replays the complete literal formula against both.

The natural-domain version substitutes each positive input plus 1, including
C and n. Its internal j0 is the natural input j, exactly as a bijective
translation requires. The total degree is unchanged. The builder generates
both versions without altering the frozen nine family.

Run `python3 nine_free_adjunct/build_nine.py` and
`python3 nine_free_adjunct/verify_nine.py` from the package root. Both use only
the Python standard library. The checks authenticate the whole source tuple,
rebuild all four circuits, expand the three source kernels exactly, verify
the finite extraction certificate, resolve the leading degree, and replay
120 actual-tuple modular assignments across both domains and certificate
forms. Binary-block, calibration, radical and CRT checks are additional
implementation audits, not substitutes for this unbounded proof.

