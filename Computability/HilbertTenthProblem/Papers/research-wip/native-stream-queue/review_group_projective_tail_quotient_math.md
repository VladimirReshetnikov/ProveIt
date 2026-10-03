# Independent mathematical challenge: the smaller group quotient offset

PASS: the positive-zero correspondence survives replacing `w+S` by `w+Z0` in the current product-radix group source. The proof needs a new pretyping bound on `E=XY`, followed by a lower-ratio argument before exponent recovery. It does not assume `X>r` at the new zero.

This review authenticates the saved 244-operation parent and thirteen accompanying source/proof files. It independently reads the rank, half-parameter and sign arguments, reconstructs the one-operand source change, and checks its exact local polynomial identities. It is a mathematical challenge with a bounded literal-source check, not an audit of a maintained child API or its degree certificate. The illustrative ten-letter table does not instantiate a numerical universal matrix alphabet.

## 1. Actual source and inherited hypotheses

The pinned immediate parent is [group_projective_product_radix_scale.md](group_projective_product_radix_scale.md), with its saved complete source in the corresponding JSON. The original positive input and fixed-table hypotheses remain in force, including the padded-program numeral margin and the current product-radix layout. In particular, the proof below is about that complete outer interface, not arbitrary independent scalar values of `q,H,M,Z`.

Write `H,M,Z` for the joined input, mask and output words, and

    Aplus=16H+13, Bpad=16M+10, F3=16Z+8,
    Z0=(q-1)F3,
    S=Aplus+(q+1)(Bpad+Z0),
    r=(q-1)S.

The source's folded A port has offset **13**. Thus the reconstructed fields are

    F1=Aplus-1-F3, F2=Bpad-F3,
    F0=q-F1-F2-F3-1,
    r=F0+qF1+q²F2+q³F3.

The last identity is an all-value polynomial identity; it is checked by an independent coefficient expansion. Omitting the `-1` when reconstructing F1 would be incorrect.

The proposed arithmetic is `X=q(w+Z0)` instead of `X=q(w+S)`. Every supplied coordinate remains strictly positive. The actual old `w` has only one consumer, `shifted_native_quotient`, and `S,Z0` are independent of it. Under

    w_parent=w_child+Z0-S,

both quotient registers, X, every later register and the entire final polynomial agree over arbitrary scalar assignments. This pullback can be negative off the zero set. Conversely `w_child=w_parent+S-Z0` is positive on every positive parent tuple: the source has `q>=16`, `H,M,Z>=0`, and

    S-Z0=Aplus+(q+1)Bpad+qZ0>0.

Only one operand is replaced. All 244 paid gates remain live, with the unchanged split 103M+141A and 36 positive witnesses. This establishes the literal coordinate identity; positivity of the opposite map requires the proof below.

## 2. Pretyping works for both joint signs

The finalizer is `U*L*(1+sum outer_residual²)-1`. At an integer zero the outer residuals vanish and U,L are units. Keep both joint signs at this stage. The direct bounds in [group_projective_joint_bound_unit.md](group_projective_joint_bound_unit.md), together with the current product-radix region estimates, use no old quotient bound. They give positive reconstructed fields, checksum `sum Fi=q-1`, residues `(1,4,2,8) mod16`, and

    q>=16, 0<Fi<q, F3>=8,
    q³+q²+q+1 <= r < q³(F3+1),
    r>=4369, Y=q(2*odd_half+1)>=3q.

The finer upper bound follows simply by bounding the three lower radix fields by `q-1`. No dyadic or Boolean-field conclusion is used.

For the proposed X, use `w>=1` and the weaker lower bound `X>=q(q-1)F3`. Then

    E >= 3q²(q-1)F3,
    3q²(q-1)F3-2q³(F3+1)
       =q²((q-3)F3-2q)
       >=q²(6q-24)>=18432.

Since the upper bound on r is strict, this proves `E>2r+3`. Also `a=Y(X+1)=E+Y>2r+3`, and `X>=16`. These are the replacement pretyping bounds. They do not assert `X>r`.

## 3. Recovering rank and the linear sign without the old bound

The actual first, main, auxiliary and strong factors all exclude -1 modulo four independently of the other equations. Consequently they equal +1. The strong equality is restored before applying the relaxed-rank lemma. The first factor is

    N0=g²+4XY²k(g-k).

From N0=1 and positive X,Y,k,g, `2XY²k+g` restores the positive odd root of the triangular first norm. The positive main root is supplied by its unchanged source expression. Put

    A=a+2, Delta=A²-1, Pfirst=2XY²+1,
    K=k-hE=r+epsilon, Jnew=2K-lambda,
    epsilon,lambda in {-1,1}.

The first Pell classification gives `k=psi_Pfirst(n)` and `n=K mod E`. Since `0<K<E`, it gives `n>=r-1`. The main norm gives `c=psi_A(p)`. The ratio slacks retain `kY<c<k(Y+1)`.

Here `Pfirst>A` requires only the new positive lower bounds, not X>r. Explicitly `Pfirst-A=XY(2Y-1)-Y-1>0`. Hence `p>n`, `p>=r`, and ordinary Pell growth gives

    c>A*Delta², c>2p,
    c>Yk>=Y(r-1)>2(2r+3)>=2Jnew.

The rank and divisibility proof in [PELL_RELAXED_AUXILIARY_PROOF.md](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md) concerns any A>1. Its actual hypotheses are now available: `c=psi_A(p)>A*Delta²` and `(ic²)²=Delta(f²-1)` with positive i. It yields

    f=chi_A(m), c divides m, m>=c>2p,
    ic²=Delta*psi_A(m).

Thus `f>chi_A(2p)>2c`, so the initially signed expression `V=of-c` is positive **before** auxiliary positive Pell classification. The odd-index identities and signed chi step-down used in [group_projective_coupled_linear_unit.md](group_projective_coupled_linear_unit.md) then give `Jnew=±p mod c`. Both Jnew and p lie in `(0,c/2)`, so `p=Jnew`. Since `n<p<=2r+3<E`, the first congruence forces `n=K`.

If lambda=-1 then `p=2n+1`. Set `Q2=2A²-1`. Its strict bound against Pfirst follows from

    Q2-Pfirst=2Y²(X²+X+1)+8Y(X+1)+6>0.

Also `2A>Y+1`. Therefore `psi_A(2n)=2A*psi_Q2(n)>k(Y+1)`, contradicting the upper ratio bound on c. Hence lambda=+1, `p=2K-1`, `n=K`. Both possible index signs epsilon remain for the next step. No complete native-selector theorem has been invoked.

## 4. Lower ratio, exponent, then index-sign exclusion

Put `r'=K-1`. It equals r when epsilon=+1 and r-2 when epsilon=-1. In both cases `r'>q>=16`, `r'>=4367`, and the restored raw equations have main index `2r'+1`, first index `r'+1`, and the two fixed minus signs. The generic parity result is compatible with the already known odd residues; it requires no original field encoding at r'.

Use only the raw lower-ratio calculation in [native_controller_binary_selector56.md](native_controller_binary_selector56.md), with `xi=(X+1)^(2r')/X^r'`. The inequalities `X>=16`, `Y>=48` and `a=Y(X+1)` give `6XY²>a`. Thus

    c/k > xi*(1+3/(2a))^(2r')*(1+1/(2XY²))^(-r') > xi.

Since `c/k<Y+1` and `xi>X^r'`, integrality gives `Y>=X^r'` and `a>X^(r'+1)`.

This is the only adjustment needed to the subsequent small-error and representative bounds. For every integer r'>=1,

    12r'<16^(r'+1),
    2*4^r'<16^(r'+1).

The first follows at r'=1 and its ratio decreases thereafter; the second is immediate. Consequently `6r'/a<1/2` and `2^(2r'+1)<X^(r'+1)<a`, using X>=16. There is no use of X>r here.

The unchanged main source gives `X=2^(2r'+1) mod(4a+3)` by the Pell recurrence. Both positive representatives are below a, so

    X=2^(2r'+1), q=2^t.

Only now use the inherited upper ratio/error estimate and binomial tail bound. They give the exact binomial integer part for Y and, since Y/q is odd and `2q|X`,

    popcount(r')=v2 binom(2r',r')=t.

If epsilon=-1, the original four fields still encode **r**, not r'. Their radix is now q=2^t; each is in `[0,q)`, so

    popcount(r)=sum popcount(Fi)>=popcount(sum Fi)=t.

But r=1 mod16 and r>1. With j=v2(r-1)>=4,

    popcount(r-2)=popcount(r)+j-2>=t+2,

contradicting the preceding identity at r'=r-2. Thus epsilon=+1. All six native factors are now +1, and the joint factor L must also equal +1.

## 5. Positive old quotient and complete theorem inheritance

The surviving branch gives `X=2^(2r+1)`. Since `q<r`, `S=r/(q-1)<r`, and `2^(2r+1)>r²`,

    X/q>r>S,
    w_parent=X/q-S>0.

It is an integer because the actual new X is a multiple of q. This is exactly the signed pullback from Section 1. Every other supplied coordinate, original input, outer field, current index and native witness remains unchanged. The all-value graph identity therefore restores the complete positive immediate-parent zero before its full typing/trace theorem is applied.

The reverse map was already positive without equations. The two maps are inverse on positive zeros, so this is a positive-zero bijection with the current product-radix parent, with the same ordinary-input relation and fixed-table hypotheses. It does not require altering the joint-bound slack or auxiliary Pell witnesses. The temporary slack normalization in the earlier pretyping proof is not part of this final map.

The child's inverse is not claimed positive on arbitrary positive tuples; the weaker initial X bound is intentional. The proof transfers the parent's effective fixed-table theorem. It supplies neither a numerical universal table nor an independently audited new degree bound.

## 6. Reproducible boundary of the check

The standalone [checker](review_group_projective_tail_quotient_math.py) authenticates fourteen files and executes no historical or proposed-author Python. Its [receipt](review_group_projective_tail_quotient_math.json) records four independent coefficient identities, the actual sole-consumer cut and all-live 244-gate source, and 32 whole-source pullbacks including eight rational assignments. All 7,808 computed-register comparisons agree.

Separate finite checks cover 495 positive padded-field boundaries, all four index/linear-sign combinations for them (1,980 cases), 256 small-error bounds, 4,096 population-change identities and 64 strong-unit residue cases. These checks support the algebra and the stated boundary; the universal inequalities, rank argument and positive-zero correspondence are proved above. No full giant Pell zero is materialized.

Run from any directory, supplying the existing WIP directory:

    python3 review_group_projective_tail_quotient_math.py --root /path/to/native-stream-queue --expect review_group_projective_tail_quotient_math.json

No repository file was changed.
