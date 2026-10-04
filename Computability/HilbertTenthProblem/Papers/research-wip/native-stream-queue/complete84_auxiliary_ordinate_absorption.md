# Polynomial absorption of the auxiliary ordinate has finite input projection

Fix a valid inherited compiler-numeral slice of the actual complete84 source. Let E be **all 70 computed registers independent of `auxiliary_quotient` and `y_aux` in its literal dependency graph**, together with **all 23 supplied ports other than those two witnesses**. Thus E contains 93 named values, including the other sixteen positive witnesses, ordinary positive input x and six fixed numeral ports. The values need not be algebraically independent.

For any fixed integer polynomial G in these 93 formal arguments, substitute `y_aux=G(E)` in the complete polynomial, keeping every other expression and supplied positive domain unchanged. Combine like monomials in G, put

    t=deg G, L=max(1,sum of absolute coefficients of G),
    B_G=3t+ceil(log_2 L).

For the identically zero G take t=0 and L=1. **Every positive zero of the substituted polynomial satisfies**

    G(E)!=0,       2d*x+b<R<=B_G.                    (1)

Consequently every such fixed substitution has finite ordinary-input projection. The conclusion allows signed G and all positive auxiliary completions. Coefficients of G may depend on the fixed compiler slice but not on the varying input or witnesses. It concerns the literal substitution, not a circuit that supplies an unconstrained new root.

This is a different result from exterior substitution for i: here the G=0 sector is empty. No generic implementation of G, gate saving, new complete circuit, global minimum or resolution of independent-gamma83 is claimed.

## 1. Literal source and inherited full-zero facts

Write

    a=R12=Y(X+1), A0=a+2, Delta=A=A0²−1,
    c=R10a, R=r_lhs, T=auxiliary_quotient, y=y_aux,
    S=aux_coefficient_root=Delta*i*c²,
    Q=R16=S²,
    V=aux_u_rhs=c(Tf−1)−R*f².

The symbol A0 denotes the mathematical Pell parameter; the source register `A` denotes Delta. The symbol T here is not `transport_quotient`. The exact auxiliary and scaled strong factors are

    Na=S²(V²−y²)+y²=S²V²−(S²−1)y²,
    Ns=Delta*f²−S².

With P5 the product of the actual first, main, input, index and transport factors, the full source is

    F84=P5*Na*Ns−Delta.                              (2)

All factors and products in (2) are paid source rows; this is only notation for the proof.

The pinned exterior-absorption theorem, Sections1 and3, and its two pinned independent reviews establish the following at every full positive84 zero on the valid slice:

    R>=3, c=psi_R(A0)>2, 0<Delta<c, 0<R<c,
    2d*x+b<R,
    Na=1, Ns=Delta,
    every one of the old 64 computed exterior values
       and old 21 supplied exterior values has absolute value<c⁴.     (3)

Here the old exterior omits all four auxiliary witnesses i,f,T,y. Those bounds cover the fixed compiler numerals, the input, the root/transport witnesses and the canonical input completion forced by the retained `gamma_sum=rho+sigma`. They do not assume a canonical auxiliary completion. Their source authentication includes the actual shifted MF convention and corrected field bounds.

Those full-zero theorems are invoked below only after obtaining a positive parent zero. They are not applied to a substituted zero with G(E)=0. Before any equation, the actual positive source already gives X,Y>0, a>0 and

    Delta=a²+4a+3>=8>1.                              (4)

## 2. Elementary auxiliary Pell index and parity

For any integer A>=2 define chi_n(A),psi_n(A) by

    (A+sqrt(A²−1))^n=chi_n(A)+psi_n(A)*sqrt(A²−1).

Every positive integer solution z,w to z²−(A²−1)w²=1 is of this form for an integer n>=1. A short descent proves this fact. The transformed pair

    z'=Az−(A²−1)w, w'=Aw−z

is integral and has the same norm. Since sqrt(A²−1)w<z<=Aw, one has z'>0 and w'>=0. Also z>(A−1)w, so w'<w. Descent ends at (1,0); reversing it multiplies by A+sqrt(A²−1) at every step. This proves the asserted integer indexing, without an assumption about a minimal chosen completion.

At a positive parent zero, Ns=Delta gives

    f²−Delta*i²*c⁴=1,
    S²=Delta*(f²−1).                                (5)

Because i>=1, c>2 and Delta>=8, (5) implies f>2c and S>f. For the latter, S²−f²=(Delta−1)f²−Delta>0. In particular S>=2.

Na=1 now gives

    (SV)²−(S²−1)y²=1.

V cannot be zero, and y>0. Applying the descent with A=S and z=|SV| yields

    |SV|=chi_n(S), y=psi_n(S), n>=1.                 (6)

The recurrence chi_(n+2)=2S chi_(n+1)−chi_n, with chi_0=1 and chi_1=S, gives

    chi_(2m)(S)=(-1)^m modulo S,
    chi_(2m+1)(S)=0 modulo S.

Since S>=2 and S divides chi_n(S) in (6), n is odd. Write n=2m+1. This argument accommodates both signs of V.

## 3. The auxiliary index cannot be smaller than the native index

There is an integer polynomial C_m(z) characterized by

    C_0(z)=1, C_1(z)=4z−3,
    C_(m+1)(z)=(4z−2)C_m(z)−C_(m−1)(z),
    chi_(2m+1)(S)/S=C_m(S²).                         (7)

The recurrence follows by taking every other term of the chi recurrence. The odd-index psi sequence satisfies the corresponding recurrence with coefficient 4A0²−2. Comparing initial values and recurrences proves the exact polynomial identity

    C_m(−Delta)=(-1)^m psi_(2m+1)(A0),
    Delta=A0²−1.                                    (8)

Indeed the first two values on the left are1 and −4A0²+1; they match psi_1(A0) and −psi_3(A0), and the alternating sign changes the recurrence coefficient to4(−Delta)−2.

Equation(5) gives S² congruent to−Delta modulo f. The literal V definition gives V congruent to−c modulo f. By (6)–(8), for one sign epsilon in {−1,1},

    epsilon*psi_n(A0) congruent to−c modulo f.        (9)

If n<R, strict increase of psi gives 0<psi_n(A0)<c. Therefore both c−psi_n(A0) and c+psi_n(A0) are strictly between0 and2c<f. Neither is divisible by f, contradicting (9). Thus

    n>=R.                                           (10)

For any integer A>=2, psi_1=1, psi_2=2A and the recurrence imply strict increase and

    psi_j(A)>(2A−1)^(j−1), j>=2.

The inductive step uses psi_(j+1)=2A psi_j−psi_(j−1)>(2A−1)psi_j. Since n>=R>=3 and S>f, equations(6) and(10) give the uniform bound

    y=psi_n(S)>f^(n−1)>=f^(R−1).                    (11)

This is a mathematical growth estimate with variable exponent, not an uncharged circuit operation. It holds for every positive auxiliary completion, not only the standard completion with auxiliary index R.

## 4. The complete 93-value interface is bounded by f³

Fresh dependency propagation through every actual source row gives exactly70 computed registers independent of T,y. Compared with the old 64-row exterior census, precisely these six rows are added:

| Added computed register | Value at a full positive parent zero | Bound |
|---|---|---|
| `L16` | f² | <f³ |
| `auxiliary_R_f2` | R*f² | <f³, since R<c<f |
| `aux_coefficient_root` | S | <f², since S²<Delta*f²<f³ |
| `R16` | S² | <f³ |
| `scaled_f_square` | Delta*f² | <f³ |
| `norm_strong` | Delta | <f |

The 23 free values are the old 21 exterior values together with i and f. Explicitly, the sixteen retained witness ports are

    Jrep,F,alpha,transport_quotient,f,h,i,s,w,tau_root,
    eta,zeta,Z,delta,rho,sigma.

The remaining seven are x and `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. The literal full lists and all 70 computed names are in the receipt.

By(5), f²>Delta*i²*c⁴>c⁴ and f>i. Therefore the old 85 values all have absolute value<c⁴<f², and both newly admitted free values are below f³. The table covers every additional computed value, including R*f². It follows that

    |E_j|<=f³ for every one of the 93 named values.    (12)

These bounds are asserted on full positive parent zeros only. No off-zero bound on an arbitrary witness or computed factor is assumed.

## 5. Signed substitution and the effective cutoff

The actual only use of the supplied `y_aux` is `aux_y2=y_aux*y_aux`. Hence the full polynomial is even in y. Moreover every argument in E is independent of y (and of T) by the literal dependency census.

At a positive substituted zero with G(E)!=0, set the parent coordinate y=|G(E)| and leave all other supplied values unchanged. The evenness identity gives a full positive parent zero, and the arguments of G keep their values. Thus all inherited premises in(3), the growth estimate(11), and all 93 bounds(12) apply noncircularly, even if G is negative on this tuple.

Each formal monomial of G has total degree at most t. Since f>=2,

    |G(E)|<=L*f^(3t).

Together with(11), this gives f^(R−1)<L*f^(3t). If R>=3t+ceil(log_2 L)+1, the opposite weak inequality follows from

    f^(R−1−3t)>=2^ceil(log_2 L)>=L.

That contradicts the strict growth bound. Therefore R<=B_G. The actual input inequality in(3) proves(1). In particular any possible input satisfies2d*x+b<B_G; a negative or empty resulting range yields no inputs. The ceiling is computed exactly as `(L−1).bit_length()` for integer L>=1.

Algebraic dependencies among the named arguments do not affect the coefficient-norm estimate. The coefficients and finite degree of G remain fixed as the input varies. Variable-index powers, an input-dependent family of polynomials, auxiliary-quotient-dependent expressions and extra supplied coordinates are outside this fixed93-argument theorem.

## 6. The zero-value sector is impossible before native recovery

At y=0, the literal auxiliary factor is Na=Delta²*i²*c⁴*V². Expanding the scaled strong factor in(2) therefore gives the all-ring identity

    F84|_(y=0)
      =Delta*(Delta²*i²*c⁴*V²*P5*(f²−Delta*i²*c⁴)−1). (13)

At any supplied positive tuple for the retained variables, (4) gives an integer Delta>1. Every other expression inside the bracket is integral, even if V, R or some factor is negative. The product before the subtraction is divisible by Delta², and so cannot equal1. Thus F84|_(y=0) is never zero there.

This proves that a substituted zero cannot have G(E)=0. It invokes no native norm sign, rank, input decoding or canonical completion. If G is identically zero, or is formally nonzero but vanishes identically after its dependent arguments are substituted, the resulting positive zero set is empty. With the stated t=0,L=1 convention the identically zero case is consistent with(1).

Consequently the whole input projection is finite, rather than only a nonzero sector. A fixed finite family of these substitutions also has finite projection on a fixed compiler slice. This prevents such a chart from preserving an infinite input language under the retained constraints. It does not identify what happens when the quotient T is also absorbed or the auxiliary equation is changed.

## 7. Source authentication and finite corroboration

The fresh helper authenticates the complete84 trio, the exterior-absorption trio and both of its proof reviews, and authenticates all twelve dependencies declared by the exterior receipt. It checks that both receipts contain the same full84 source and that the old receipt binds its helper bytes. All inputs are inert files; no predecessor code is imported or executed.

It visits all 84 instructions, checks 33 named literal boundary rows, recomputes the old 64+21 and new 70+23 dependency censuses, and verifies the sole direct y consumer. The unchanged full source is saved as evidence, not as a new circuit. No implementation or operation count for a general G is emitted.

For the symbolic proof it processes the full source three times under y,−y,0. Only 60 actual values already proved independent of all four auxiliary ports are used as symbolic cuts. In particular `norm_pair`, `norm_triple`, `c2` and `Ac2` are expanded at their true producers, as are the scaled strong factor, all new auxiliary producers and the complete finalizer. The resulting 17-term polynomial agrees with a separately formed factor expression. Evenness is exact, and the 13-term zero-y expansion agrees with(13). Thus the zero-sector proof is authenticated through all actual rows, not only through a handwritten finalizer formula.

Thirteen C_m coefficient lists corroborate 91 odd-index identities. There are 182 parity,175 descent and 168 strict-growth component checks,70 checks separating both signs at smaller indices, and234 degree/coefficient-norm cutoff cases tested at four bases. These are finite standalone arithmetic examples, not compiler histories, complete native zeros or substitutes for the quantified proofs above.

The eight direct pins are:

| File | SHA-256 |
|---|---|
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| complete84_exterior_auxiliary_absorption.py | `46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9` |
| complete84_exterior_auxiliary_absorption.json | `ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b` |
| complete84_exterior_auxiliary_absorption.md | `69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de` |
| review_complete84_exterior_auxiliary_absorption.md | `df47a59713fca80a9a059bda9b2a5956774d67ebcd60b5ce99b54096414eee3a` |
| review_complete84_exterior_auxiliary_absorption_math.md | `bdf25d1eb78850aa434ead4cf5fb2b62c2c8318413c55c9bcd73d6ca55d0b0d4` |

The twelve transitive pins, complete census, literal source, exact coefficients and finite records are also saved in the receipt. The helper uses only the standard library, rejects duplicate keys and noninteger JSON numbers, uses checks that remain active under optimization, and compares receipts by canonical type-sensitive JSON. Its bytes are bound into the receipt.

Replay with `--root ABS_WIP` and `--expect RECEIPT`; `--output NEW_PATH` instead creates a fresh receipt exclusively. The writer and fresh normal and optimized exact replays from working directory `/` passed, using absolute source, root and receipt paths. No repository or frozen predecessor was changed.

New helper SHA-256: `9d8ea463330b31dea1af8187784981b576c932a3799ca45a5dabfe2ea0bc2c94`.

New receipt SHA-256: `8101345c3c6588539fe56f340322ba573e66ce66b978db7da8154781c23547f8`.
