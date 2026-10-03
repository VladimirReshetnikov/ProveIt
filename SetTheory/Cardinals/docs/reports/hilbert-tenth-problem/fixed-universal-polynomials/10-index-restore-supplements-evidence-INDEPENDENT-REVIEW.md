# Independent audit of the raw/positive restored-index reduction

## Verdict and limits

**PASS for the stated necessary-condition reduction on valid fixed compiler slices with strictly positive supplied witnesses.** I found no mathematical correction needed in the reviewed reduction. In particular, the actual compiler supplies the previously unverified bound

    0<DC<B, 0<DR<B, K0=DC+B*DR<=B^2-1.

Together with the independently reviewed bootstrap, the literal raw29/positive21 child equations prove

    R=+p or R=-p, p odd, p>=13, q even,
    v=u or v=uA, u=2*d_cell*x+b.

On the negative branch they force

    E/3+1<=p<X*q^4, s<3q,
    1<=t<3q/s, 2n+p-1=tE,

and the even input alternative v=uA forces us<q. These are necessary conditions, not a resolution of R>0 and not a raw29/positive21 counterexample. The distinct signed19 branch lacks supplied positive W, so neither this reduction nor a counterexample there transfers automatically between the domains.

The reviewed reduction snapshot has SHA256
`0ae2f56e7db3177f3100198ae503c950d2f11d30d3d6d55d51f399dbdbeb48a9`.
The reviewed bootstrap proof snapshot has SHA256
`581e2192aa156dd82ad3450bd8ce85444cf4bf06c0a4814a88b867f964eeb033`.
The bootstrap independent-review snapshot has SHA256
`958c27cba7ad0e0c8121dd66b4ae66e86c84fd6b0756f8316a9ada8b2053a9d5`.

All upstream sources are pinned to ProveIt commit
`2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`. All 21 cached source files were authenticated by recomputing Git blob SHA1 and SHA256. Five additional sources were retrieved read-only from GitHub to close the numeral-alias and inheritance chain: four have source SHA256 values matching the relevant parent/child receipt pins; the additional complete80 alias source was authenticated against its returned Git blob identity. Full hashes, byte counts, and exact commit URLs are in `source_manifest.json` and the appendix below.

No upstream Python module or arithmetic schedule was run. Python sources were read as text and parsed as AST data; JSON schedules were inspected and structurally compared as data. Only the newly written independent checker was executed. No original research source, upstream repository, or report package was changed.

## 1. Literal equations, positivity, and source ports

The source receipts continue to label the modes by their parent names `raw30` and `positive22`; the index-eliminated children actually have 29 and 21 supplied witnesses. The independent checker reconstructed the transformation from the complete parent receipts, rather than trusting the reported counts:

- All 72 common rows remain with only `r` renamed to `restored_r`
- `r1=r+1` and `R11=r1+hpm1` disappear
- `hpm1=h*UM` stays, followed by `index_partial=actual_k-hpm1` and `restored_r=index_partial-1`
- Both the packing comparison and `H17=jc-restored_r` use that same expression
- Exactly the comparison `actual_k=R11` and witness `r` disappear
- Every retained comparison and both entire SOS finalizers match the literal expected lists

Here actual_k is supplied `k` in raw29 and computed `R10b=eta+zeta` in positive21. No off-zero replacement of raw `k` was made. An integer zero of the SOS therefore makes every retained residual zero. This use of SOS positivity is not an arbitrary-ring assertion.

The outer child rows directly give the following equations. They are not imported from the older theorem's positive-index conclusions:

    q=(B-1)J+1,
    C+alpha+2*d_cell*x=q,
    (K0+X)C=F+z(q-1),
    C=Z+W,
    R=(q^2-Z-qF)(q^2-1)+(MC+q*MF_source)J.

In raw29, `C,W,Z,q` are supplied and the requisite comparisons are retained. In positive21, `C` means the register `marked_rhs=Z+W`, and `q=repunit+1`; the raw-bound and transport comparisons are retained. Both modes supply strictly positive W and Z. Consequently

    q>=B>=16, 0<Z<C<q, 0<W<C<q,
    0<2*d_cell*x<q, F<(K0+X)C.

The input block retains

    kappa=u+delta*Delta, c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H,

where `u=2*d_cell*x+b`, `A=a+2`, `Delta=A^2-1`, and `H=4a+3`. Raw29 supplies kappa and mu and retains all comparisons. Positive21 computes kappa as `index_rhs` and mu as `exponent_rhs`; both are sums/products of strictly positive quantities. Its retained `R10a=pell_gap` comparison supplies c>kappa. Thus the positive input Pell classification is available in both modes without R>0.

By contrast, signed19 computes `W=marked_rhs-Z` and has no supplied W or retained positive gap witness phi. This is the exact domain boundary that prevents importing its construction into raw29/positive21.

### Exact fixed-numeral aliases

The reduction's interpretation of the fixed ports is also literal source provenance:

1. [complete80, lines 23–24](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_80.py#L23-L24) defines `Bm1=B-1` and `Kconstant=DC+B*DR`
2. [complete76, lines 28–31](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py#L28-L31) calls that exact inherited environment through complete77→complete78→complete80, then sets `twice_cell_bits=2*cell_bits`
3. [half-binomial source, lines 31–33](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial.py#L31-L33) replaces the schedule's `MF` port by native `MF+B-1`
4. [positive elimination, lines 139–142](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_elimination.py#L139-L142) makes the same fixed-input replacement
5. Both complete74 rewrites preserve the fixed ports and all relevant literal gates

Hence Kconstant really is K0, and the source port `MF` really is MF_source rather than the native mask. The outer estimate does not assume a favorable arbitrary assignment to the free numeral ports.

Notation warning: the raw source witness named `d` is the main Pell root, whereas the compiler's `cell_bits` is d_cell. The source register named `A` is mathematical Delta, not mathematical A. The source auxiliary `ic2` is i*c^2, not the outer repunit J or input rho.

## 2. Complete compiler provenance for K0<B²

This bound follows from the actual compiler interface `new_constants(compile_windows(windows, alphabet_size))`. The proof below covers the optional high-monomial branch and the change to the inner radix before numeral export.

### 2.1 Sparse layout and coefficient bound

In [complete76, lines 94–148](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py#L94-L148), let S be the sum of the positive center coefficients, Emax the maximum native position, M0 the anchor spacing, and g=`high_degree`. DCpoly is obtained by adding:

- Four unit monomials, at exponents 3a_tiles, Hcomp+a_tiles, 8M0, and 24M0
- Two copies of every center coefficient, at T1-e and T2-e
- Either zero or one additional unit monomial at g

Thus its total coefficient mass is exactly 2S+4+epsilon, with epsilon in {0,1}. Coincident exponents merely add positive coefficients. Every resulting coefficient is at most 2S+5.

The layout has

    Hcomp=Emax+24M0+3a_tiles+1,
    T1=Hcomp+2Emax+a_tiles+1,
    T2=T1+2Emax+1,
    g=T2+Emax+1,
    L=next_five_power(g+Emax+1).

Every center-coefficient exponent e lies in [0,Emax]. Hence all Tj-e are positive and at most T2. The four unit degrees are positive and below g. The optional degree is exactly g. Since L>=g+Emax+1,

    0<min(support DCpoly), max(support DCpoly)+Emax<L,
    0<Hcomp<T1<T2<g<L.

These follow from the formulas, not merely from executing source assertions.

### 2.2 Stronger radix and parity

[Half-binomial compiler, lines 21–42](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py#L21-L42) first receives that sparse complete76 object and leaves DCpoly, Hcomp, and L unchanged. Writing K for the number of native positions, it chooses

    mass=(K+2)(2S+6),
    target=max(4mass+8,2mu_comp+4,16),
    b=next_five_power(bit_length(target-1)), Rrad=2^b,
    d_cell=bL.

The helper next_five_power returns the least power of five at least its argument. Since 2^bit_length(target-1)>=target, Rrad>=target. Therefore each DC coefficient is strictly below Rrad. Both b and L are positive powers of five, so d_cell is positive and odd. Also b<B=2^(bL), as claimed in the reduction.

### 2.3 Inheritance and cache timing

The complete76 class body is empty. The complete77 class inherits complete78's class and overrides only `MC` and `constants()` ([lines 75–84](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_77.py#L75-L84)). The underlying complete78 dataclass has neither a custom constructor nor a post-init hook. Its relevant materializers are ([lines 95–105](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_78.py#L95-L105)):

    B = 1 << d_cell,
    DC = sum(coeff << (b*exponent) for each DCpoly term),
    DR = 1 << (b*Hcomp).

B, DC, and DR are cached properties, but complete76.compile_windows constructs only sparse fields and never accesses those properties. Its wrapper raises b and d_cell before the first export and likewise never accesses the properties beforehand. Therefore no stale numeral computed at the old radix survives this path.

Finally [new_constants, lines 45–57](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py#L45-L57) materializes `dict(cc.constants())` and changes only MC and MF. DC, DR, and B are unchanged. The compiler proof explicitly identifies this as the required export interface; plain constants() alone would export the old masks.

### 2.4 Result

All nonzero DC digits lie at exponents below L and are in [1,Rrad-1], so

    0<DC<=sum_(e=0)^(L-1) (Rrad-1)Rrad^e=B-1.

Also 0<Hcomp<L gives 0<DR=Rrad^Hcomp<B. Thus

    0<K0=DC+B*DR<=(B-1)+B(B-1)=B^2-1< B^2.

Since q>=B, K0<=q^2-1. This proof is independent of R's sign, mask decoding, q being a power of two, or correctness of a simulated computation. It applies to valid compiled numerals, not arbitrary values assigned to the fixed ports.

## 3. Bootstrap dependencies and exact representative

The bootstrap was checked against its independent review and the pinned underlying first-norm, strong-rank, odd-quotient, and plus-sign step-down proofs. Only their stated elementary subarguments are used; the whole positive half-binomial theorem is not applied on a negative branch.

The available conclusions are

    X=wq^3, Y=sq^3, E=XY, a=Y(X+1),
    c=psi_A(p), p odd and p>=13,
    R=+p or -p modulo c,
    k=2psi_P(n), P=2XY^2+1,
    (p+1)/2<=n<=p-1, 2n=R+1 modulo E,
    c>2p and c>=(2A-1)^(p-1)>A^12.

In particular, U positivity was obtained from the retained equation U=of-c and the relaxed auxiliary rank bound f>2c. It was not assumed from U=jc-R. Likewise the lower bound p>=13 was obtained from main projection and rank parity, without R>0.

### 3.1 Remainder bounds without power decoding

Let

    S'=Z+qF-1,
    T'=MC*J+1+q*(MF_native*J-1).

Native mask bounds 0<MC,MF_native<B-1 and the repunit equation imply 0<T'<q^2-1 without needing q=B^N. The paid shifted source is exactly

    R=(q^2-S')(q^2-1)+T'.

The difference before imposing the repunit equation is q((B-1)J-(q-1)). Thus R cannot be zero and, as S'>=q, R<q^4.

For R<0, the original source's mask term is positive. Dropping it and its other favorable terms, and then using Z<C and F<(K0+X)C, gives

    -R<(Z+qF)q^2<Cq^3(X+K0+1/q).

Because K0<=q^2-1 and X>=q^3,

    K0+1/q<q^2<=X/q.

With integral C<=q-1,

    -R<CXq^3(1+1/q)
       <=(q-1)Xq^3(1+1/q)
       =Xq^4-Xq^2<Xq^4.

The positive branch already has 0<R<q^4<Xq^4. Therefore |R|<Xq^4 on either branch. Since A>XY>=Xq^3 and q>=16, A^2>2Xq^4; the bootstrap consequently gives c>A^12>2Xq^4. Hence |R|<c/2 and p<c/2. The congruence R=±p modulo c can now have only its zero multiple of c, proving the exact alternatives R=p and R=-p.

### 3.2 q parity

Both alternatives make R odd. If q were odd, B even and q=(B-1)J+1 would force J even. In the original packing expression, q^2-1 and J would both be even, so R would be even. Contradiction. Hence q is even, and therefore X,Y,A are even and Delta is odd. No power-of-two conclusion follows merely from this parity argument.

## 4. The negative branch remains a bounded window

If R=-p, the first-index congruence becomes

    2n+p-1=tE

for an integer t. The reviewed n interval gives

    2p<=tE<=3p-3.

It follows that t>=1, p>=E/3+1, and, combining with p<Xq^4,

    Y<3q^4, s<3q, 1<=t<3q/s.

Here t is a new congruence quotient, not the source witness h. The exact packing equation additionally requires

    p=(Z+qF-1-q^2)(q^2-1)-T', F>=q.

Indeed R<0 requires S'>q^2, while Z<q. At the boundary F=q this requires Z>=2. Thus importing F<q from the original positive-index proof would discard the branch one is trying to exclude.

For fixed q,X,Y and compiler numerals this bounds p and t finitely. There is no uniform bound as q and X vary. The existence of an infinite negative family for an isolated kernel at fixed X,Y does not establish that any member falls in this outer-source window.

## 5. The actual input block gives exactly the asserted dichotomy

The positive input norm supplies unique v>=1 with kappa=psi_A(v) and mu=chi_A(v). The retained strict gap c>kappa gives v<p. On either sign branch,

    p=|R|<Xq^4<Delta,

because Delta>(XY)^2>=X^2q^6>Xq^4. The raw bound and b<B<=q give 0<u<2q<A-1, so both u and uA lie strictly between zero and Delta.

Reducing the Pell recurrence modulo Delta gives

    psi_A(v)=v mod Delta for odd v,
    psi_A(v)=vA mod Delta for even v.

For odd v, kappa=u modulo Delta implies v=u because both v and u are in (0,Delta). For even v, multiplying vA=u modulo Delta by A, with A^2=1 modulo Delta, gives v=uA modulo Delta; both v and uA again lie in (0,Delta), proving v=uA exactly. There is no illegitimate replacement of vA itself by a least representative here.

Since u is odd and A even, uA is indeed even. If that alternative occurs on the negative branch, uA<p<Xq^4 and A>XY imply uY<q^4, equivalently us<q. In fact this conditional inequality follows from the common absolute bound on either branch; on the positive branch the stronger p=R<q^4<A already excludes v=uA outright.

The input projection yields W=2^v modulo H with 0<W<q; the main projection yields X=2^p modulo H. Neither p<Delta nor v<p is an exponent no-wrap bound. This audit supplies no justification for replacing those congruences by equalities on R=-p.

## 6. Clarifications, reproducibility, and the remaining obligation

No mathematical change to the reduction is required. Useful presentation clarifications are:

1. Call the children raw29/positive21 while explaining the receipt's inherited raw30/positive22 mode labels
2. Distinguish compiler d_cell from the raw source's main-root witness d, and mathematical A from source register A=Delta
3. Include the exact complete80 and half-binomial fixed-input alias chain above, in addition to the DC/DR materializer chain
4. State explicitly that the mask remainder bound uses only the native mask ranges and repunit equation, not q=B^N
5. Keep the signed19 result and all isolated-kernel or outer arithmetic fixtures separate from a full raw/positive zero

The newly written checker `audit_reduction.py` can be run from any working directory. It reads the cached upstream files as data only. It checks all source hashes, the two source SHA256 receipt fields, available immediate source pins, literal child transformations and complete finalizers in all three modes, and static compiler class structure. Its supplementary arithmetic checks pass:

- 64,184 cases of the sharpened outer estimate, using exact rational arithmetic
- 3,564 outer arithmetic fixtures, including 1,980 with negative R and 1,620 odd-q parity cases
- 1,353,198 discriminant-congruence cases, with 4,950 hits each for v=u and v=uA

These finite fixtures are neither full kernel zeros nor compiled universal instances. They corroborate the displayed unbounded proofs and test both sides of the input dichotomy; they do not prove the theorem by sampling.

The checker SHA256 is
`03dc4c921d3a124a788f053fcd25cd9f5d8c81e7799fabbaa704d0e374410648`.
Full results and proof/checker snapshot hashes are in `audit_results.json`.

The remaining task in these two domains is still to exclude, or fully realize, R=-p while satisfying every retained norm, ratio, first-index, input, transport, and projection equation in this bounded window. In particular, the quotient interval

    Y<psi_A(p)/(2psi_P(n))<Y+1

and the modular exponent conditions remain essential simultaneous constraints. This audit does not establish positivity, a raw29/positive21 full counterexample, a universal positive-domain equivalence, or a new operation/witness bound.

## Appendix: exact source identities

The table below is generated from the independently verified manifest. Every URL fixes the same commit stated above.

| Source | Git blob SHA1 | SHA256 |
|---|---|---|
| [complete75_half_binomial_compiler.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md) | `90aa8895f38e2f9cb3a13c7ecff9f3f2a8d1fbf3` | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| [complete75_half_binomial_compiler.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py) | `d9e24d78b66d123b5ffe4891c5e960de015b9794` | `d6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2` |
| [explore_fixed_raw_universal_76.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py) | `c0eb251339f9427a62e9484825be7cffea0bc293` | `011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0` |
| [explore_fixed_raw_universal_78.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_78.py) | `685efc8fe8c5e1f73dea5814efe97f3aaaa6b5d5` | `10d5ed5809ccaf49b6006cf5758a40ed4f2bd05fed3f4747add3ea4c5d0b1639` |
| [FIXED_RAW_UNIVERSAL_76_PROOF.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md) | `d0712f0258a5fc0959980803d5b5a8a02b5889cb` | `75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87` |
| [explore_fixed_raw_universal_77.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_77.py) | `35c38f27d3aa6e2c9a1048a2d340321d9aef0aa9` | `9222a13dc180bd2361877674c4bd957d18f2d9aef827852cf5d320a3d7ac7d7a` |
| [review_complete74_nonlinear_index_projection.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete74_nonlinear_index_projection.md) | `a1623c4ff5761cdf3ea73e6b4de04f4507aab3a2` | `85c0e832b0af7f1ee12a042d97df34481a274f035f150c00f1686cdd58da9ed3` |
| [complete74_factored_first_norm.json](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.json) | `6aaaf69a6104ebfffd9e08a6331166c661a60847` | `7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28` |
| [complete74_nonlinear_index_projection_scout.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.md) | `7aab55c0081d068b0088373647455d62bda50bf7` | `2034e1343f9c4c059525445c6ef1ae287dec48c0da9d9d27123f1e5745c2c40d` |
| [complete75_signed_projection_elimination101.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_signed_projection_elimination101.md) | `cb0da6c1a870e374a774a5bfe37801f23d04797e` | `55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d` |
| [pell_kernel_half_binomial42.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md) | `0a7d1298b31d9e5c1371fa7a30b6787ca5ee09c1` | `0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992` |
| [PELL_RELAXED_AUXILIARY_PROOF.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md) | `30d01973aeeca8eb5d29b0da94aa7b56bff074ca` | `9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90` |
| [HALF_PARAMETER_PELL_92_PROOF.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md) | `d6450d0608efb5bcc732256c096db1ee85817a16` | `c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b` |
| [EXPLORATION_FIXED_MINUS_INDEX_PARITY.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md) | `f9c3e073957dbb35e55d250b2a456eb1aa16b8dd` | `47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b` |
| [complete75_asymmetric_scale_tradeoffs.md](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md) | `db70d23cd1e9a03be0ea7a70a4be1b61f71e77d5` | `3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2` |
| [complete74_nonlinear_index_projection_scout.json](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.json) | `60f726116071b587601dc2d7e4e318ae39b021a1` | `ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92` |
| [complete75_half_binomial.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial.py) | `6ad06d7c27393eefb641eeaa623294492213aeef` | `5383b009a41abc19bb4c94e3f25c96ccfd4122d6a016c27b54fda0a75f7acab5` |
| [complete75_positive_elimination.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_elimination.py) | `e45d721663421c90ea186a1e5b97517eb7b87a81` | `70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749` |
| [complete74_factored_first_norm.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.py) | `6e10a2538e8cb4026569197ef4b893f18bc3c03d` | `7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908` |
| [complete74_nonlinear_index_projection_scout.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.py) | `096d3b3e84e3b2c02bc32368bc437837aa5e0c08` | `610739f1074ad792e8010287e8e162d509832c8d5e7444dc38ecae98e7710c71` |
| [explore_fixed_raw_universal_80.py](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_80.py) | `d2b77ceb8293538a5e555a55760c7cdfc2168152` | `04a5522292b2348e4a1b52b5a5acb29a493e7f0bec46be4288b007ec762f6e2b` |
