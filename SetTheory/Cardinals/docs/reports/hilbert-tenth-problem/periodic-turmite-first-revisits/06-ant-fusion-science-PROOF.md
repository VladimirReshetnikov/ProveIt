# Fusing the structured coefficients with spatial Horner evaluation

This is a new, separate construction. Reports44 and47 and their frozen releases
are unchanged. The claim concerns equality of the complete final integer
polynomial for every assignment of the same coordinates, not just its zero set.
The ant-dynamics dependencies and all inherited caveats remain unchanged.

## 1. Objects inherited from the frozen coefficient theorem

Write S=576000, N=960, D=600, R=601547591, V=240619037200,
u=2V and Z=3^400. The fixed 400-digit signed profiles Q[a,d], fixed
occurrence constants T[a,s], unsigned profiles H,B,F, and cut profiles
Hlow,Hhigh have the meanings and exact geometric justification in Report47.
Here a is one of DUP,NAND,MOVE_LEFT,MOVE_RIGHT, 0<=s<=956,
and 0<=d<1200. We read only the authenticated finite masks and own-code
arithmetic specifications. There is no ant, tape, color-recipe or saved-schedule
execution. Small masks are ordinary compile-time finite data; no tile integer,
occurrence integer or final polynomial coefficient is instantiated.

For any fixed array A indexed modulo S, define the ordinary polynomial

    E_phase(A;W) = sum(j=0..S-1) A[(288650-j-phase) mod S] W^j.

Only phase=0 and phase=S/2 occur. Every displayed modulo operation computes a
fixed compile-time index or nonnegative integer exponent. W is unrestricted.
No quotient ring, negative exponent, division or W^S=1 identity is used.

## 2. The correction convolution has twelve short factors

Let I0=[0,50], I1=[51,650], I2=[651,1199], inclusive, and set

    Q[a,b](W) = sum(d in Ib) Q[a,d] W^(50+600b-d)
    L[a,b,phase](Y) = sum(s=0..956) T[a,s]
                           Y^((480-b-s-phase/600) mod960).

The exponents of every Q[a,b] are between0 and599. For every s,d in Ib,

    (288650-phase-600(s+1)-d) mod576000
      = 600*((480-b-s-phase/600) mod960) + 50+600b-d.

The right side belongs to [0,575999], and differs from the un-reduced left
side by an integer multiple of576000. This proves the equality as an identity
of ordinary nonnegative exponents, including the two wrap boundaries.
Consequently, if C is the Report47 correction array, then

    E_phase(C;W) = sum(a,b) Q[a,b](W) L[a,b,phase](W^600).

For each a,b,phase, the map from s to the length960 coefficient position is
injective; the three unoccupied positions contain the paid zero expression.
Our literal source uses twelve full length600 Horner polynomials and twenty-four
full length960 Horner polynomials. Zeros are retained in the Horner grammar.
Each of the24 products is paid, and each twelve-term phase sum costs11 additions.
It shares the twelve Q factors between phases and constructs Y=W^600 once.
The identity holds coefficientwise with T and Q treated as independent formal
symbols; it is therefore stronger than numerical tests at particular W.

## 3. Exact finite block compression

For an unsigned profile A and a phase, partition the S positions into the960
consecutive600-position blocks. Group blocks only when all600 profile masks are
identical. If b_g[r] is one distinct block and J_g its set of block positions,

    E_phase(A;W) = sum(g) [sum(r=0..599) b_g[r]W^r]
                              [sum(k in J_g) (W^600)^k].

The source verifies that J_g partitions all960 positions. The emitted evidence
records the digest of each block's complete mask tuple and every position in its
group. Expansion therefore gives an exact array equality, rather than a sampled
or approximate periodicity assertion. At phase0, the distinct block counts are
H=5, B=4, F=6, Hlow=3, Hhigh=5 and first=4. PhaseS/2 merely rotates the block
positions by480, preserving the same block contents and counts.

For a maximal consecutive run [k,k+l-1] in J_g its weight is

    Y^k (1+Y+...+Y^(l-1)).

The source explicitly constructs powers by binary chains. It builds the geometric
sum together with the power using

    P_2n=P_n^2, G_2n=G_n+P_n G_n,
    P_(2n+1)=P_2n Y, G_(2n+1)=G_2n+P_2n.

All operations are paid. The initial pair is (Y,1). A length1 geometric sum
aliases literal1; a zero exponent aliases literal1. Their products are omitted
only where explicitly specified in the grammar, not discounted after counting.
Thus the formulas are valid at W=0,1,-1 and every other integer.
Identical coefficient-wire tuples share spatial Horner blocks; identical sets
of block positions share weight polynomials; Y powers and geometric sums are
cached explicitly. These sharing rules are part of the deterministic source.

## 4. Fused Tile and first polynomials

Let G=sum(r=0..R-1)Z^r and put

    U_phase = G E_phase(B;W) + E_phase(C;W)
    Full_half = E_half(H;W) + Z U_half + 3^(V-400) E_half(F;W)
    Cut_0 = E_0(Hhigh;W) + 3^375 U_0 + 3^(V-425) E_0(F;W)
    TilePolynomial = Cut_0 + 3^(V-25) Full_half
                                      + 3^(u-25) E_0(Hlow;W).

Linearity and the exact Report47 Tile[x] identity prove

    TilePolynomial = sum(j=0..S-1) tile:j W^j.

The first polynomial is E_0(first;W), where first[x] is bit25 of H[x].
These are precisely the two formerly dense initializer Horner expressions.
We do not replace the whole background by a zero-set-equivalent constraint:
the existing initializer still computes its original

    hy * (hx*TilePolynomial + Wp*FirstPolynomial)

and every subsequent consumer of this expression is retained.

## 5. Complete source binding and unchanged finalizer

`fusion_source.py` first authenticates its locally copied own-code Report47
occurrence compiler, own-code Report44 arithmetic generator, and all finite data.
The entire occurrence construction is retained. All small profiles are built by
the Report47 literal1/3 signed-ternary Horner grammar, with the same cache inventory,
even if a profile is unused after fusion. The five fixed shifts, G, all584 anchor
rows (220 multiplications and220 additions each), and all remaining named and
small constants are also retained and paid. Only 598 named constant ports remain;
tile/first coefficient ports are no longer needed.

The old main source is actually regenerated by the authenticated owned generator.
Its original canonical hash must equal the Report44 target for each arity.
The adapter recognizes exactly the two complete dense Horner intervals and checks
every multiplication/addition record in them against the prescribed recurrence.
It removes 4*(576000-1)=2303996 old gates. Their final outputs are bound to the
fused TilePolynomial and FirstPolynomial. All other removed intermediate outputs
are marked unavailable: any outside reference would make generation fail.

Every other old arithmetic record is retained with a total topological operand
map. Fixed constants bind to paid expressions (or literal1/3), declared coordinates
remain unchanged, and earlier retained gates bind to earlier new gates. The
fused expressions are generated immediately before the old tile Horner interval,
after their W coordinate expression exists. All raw/positive declarations,
285/286 residual metadata records and the complete original sum-of-squares
finalizer are preserved. The sole final equation has the last gate on the left
and paid gate0=1-1 on the right. No C: coefficient operand remains.

Induction on the unchanged main operations, substituting the two proved
polynomial identities at their checked intervals, proves exact pointwise equality
of all preserved gates and the final polynomial. Hence the positive witness
domains and counts remain465/467, the number of asserted equations remains one,
and the exact variable degree remains2304000. The degree statement follows from
polynomial equality, not from a syntactic degree estimate that ignores zero
coefficients or cancellations in this new factorization.

## 6. Count and evidence scope

`fused-receipt.json` contains exact M/A counts, canonical complete-source hashes,
all stage counts, the verified old-main hashes, positive-domain digests, removed
intervals and final paid-zero equations. Arithmetic is TSV id/op/operand/operand;
metadata is compact JSONL, as in the Report47 joined source. The new stream is
actually generated, topologically checked and hashed; it is not materialized as
giant integer values. `checks.py` separately verifies every correction exponent
identity and tests the new expression against independently dense finite-field
evaluation, including W=0 and±1. Such modular checks supplement the algebraic
proof; they do not replace it or prove the inherited ant-dynamics theorem.

This directory is a research candidate until independent audit. It makes no
optimality or novelty-priority claim and does not modify the frozen Report47 result.
