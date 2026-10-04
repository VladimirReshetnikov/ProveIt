# Balanced convolution for atomic selected-output blocks

The complete fixed-table source uses **2,462 operations = 1,124M + 1,338A**, **150 positive integer witnesses**, and has exact degree **35,587**. It saves **700 operations (343M and 357A) and two witnesses** against the frozen [3,162-operation packed-output source](matrix193_packed_output_scout.md). Its degree increases from 34,817. The complete diagnostic uses 302 operations and 55 positive witnesses, with exact degree 1,363.

The controller, 340 physical selection slots, ordinary input, fixed program recipe and one native history kernel remain unchanged. The new source removes the two word-sum extractions and the four long selector-center corrections. It first centers each entire selected block, then multiplies by signed coefficient polynomials and extracts their middle coefficients through paid balanced remainder equations. All supplied coordinates are positive integers; signed high quotients are differences of two positive supplied coordinates.

This is a complete fixed-program upper construction, still above the universal 84-operation bound. Arbitrary assignments to the fixed coefficient ports and the illustrative diagnostic are not claimed to be universal programs. The prior 3,162-operation artifacts are unchanged.

## 1. Reused packing and fixed constants

Use exactly the atomic table, group order and valid coefficient recipe from the [packed-output proof](matrix193_packed_output_scout.md). The original table has n=99 controller edges, m=128 controller slots, 72 X groups, 96 Y TILE groups, one LOAD and one SWITCH. The edge IDs remain LOAD 0, SWITCH 1, TILEs 2–97 and IDLE 98.

There are two fixed selected blocks of lengths l_X=144 and l_Y=194; the latter includes LOAD. Two context-SWITCH lanes follow them. The diagnostic uses lengths two and two, plus two SWITCH lanes, with m=8. Its Hfix is the parent's 9; the actual-table recipe uses Hfix>=max(m,340), larger than every absolute initial coordinate. The eight fixed coefficient ports are unchanged and are not witnesses.

Keep

    D=x+Hfix+height_slack, c0=D-1, B=K D,
    E_e=Ehat_e-1, J=sum_e E_e, P=(B-1)J+1,
    Q=C P.

K is the same fixed dyadic radix multiplier, at least 32 and larger than one plus every relevant matrix column absolute sum. For each fixed block let a_(j,l) be its coefficients from M_g-I. Define M_block=1+max|a_(j,l)| and let C be the least power of two strictly exceeding both 2M_block*l_block. Thus the actual source retains

    M_X=17381989392455015642208733,
    M_Y=392491491,
    C=2^93=9903520314283042199192993792.

The diagnostic retains M_X=M_Y=2 and C=16. No coefficient offset is added to the signed coefficient words; M_block is now only a bound used to choose C.

Compute the two selector blocks

    S_block=sum_g S_g*(Q^(2g)+Q^(2g+1)),                    (1)

where g is local to the block. The source shares these with the physical mask:

    Mphys=(B-1)*(S_X+Q^l_X*S_Y
                       +Q^(338)*(1+Q)*S_SWITCH)             (2)

in the actual table; the diagnostic uses exponent ell-2=4 in place of 338. Expanding (2) gives precisely the old physical mask, for all integer supplied values. Splitting the old Horner pack changes no native input field. Every multiplication, polynomial evaluation and lane-shift power in (1)–(2) is emitted and charged.

The new source also computes Qhalf=(C/2)*P by a paid fixed-coefficient multiplication. Since C is an even fixed numeral, this is Q/2 identically over integer supplied values. No division gate is introduced. For a block of length l it computes

    T=Q^(l-1), T_half=Qhalf*Q^(l-2)=T/2.                    (3)

Here l>=2 in both arrays; all exponents are fixed table constants. There is no duration-dependent exponent, reversal of the time history, or uncharged dilation.

## 2. Typing precedes the signed convolution argument

The nonnegative selected block remains supplied through Z_block+1. Its positive block slack enforces

    Z_block+block_slack=Q^l.

The same joint sum G=sum_i H_i+Zhat_SW0+Zhat_SW1+bound_global is retained. The output is the integer native product times 1+SOS, minus one. At a positive integer zero all twenty outer comparisons vanish and the native product is one. Hence G-P=±1, G>=7 and P>=6. J=0 would give P=1; therefore J>=1 and P>=B. The valid fixed recipe supplies the inherited native threshold, including P>=B>=320 for the diagnostic.

These facts, the two block bounds, and S_g<=J give exactly the pretyping bounds from the packed-output proof. The native truth fields are positive with the required residues before one-hot or AND decoding is invoked. The unchanged bootstrap yields dyadic q, B and Q, then dyadic P because Q=C P. It recovers P=B^t, the one-hot controller, the range bounds, and the joined AND.

In particular the canonical Q-block coefficients satisfy

    Z_l=H_(row(l)) AND ((B-1)*S_(group(l))),
    0<=Z_l<P.

The group selector words are Boolean in radix B, and each shifted state digit is at most 2D-1. Thus

    U_l=Z_l-c0*S_(group(l))

is the selected signed state word. Each selected state digit is between -(D-1) and D, so

    |U_l|<=D*J<P.                                          (4)

The last strict inequality follows from P=(B-1)J+1 and B=K D with K>=32. No extraction equation is used to prove (4).

Now compute the entire signed selected block by two paid gates:

    U_block=Z_block-c0*S_block=sum_l U_l Q^l.                (5)

This is a polynomial identity. The right side is a signed coefficient expansion, not a claim that U_l are ordinary nonnegative radix digits; borrowing in the integer value of (5) does not invalidate the expansion.

## 3. Balanced middle coefficient and the entire low tail

For each of the four fixed output coordinates, emit the signed reversed coefficient polynomial

    A_j(Q)=sum_(r=0)^(l-1) a_(j,r) Q^(l-1-r),
    F_j=A_j(Q)*U_block=sum_(h=0)^(2l-2) c_h Q^h.            (6)

Its middle coefficient is exactly the desired unshifted matrix increment

    d_j=c_(l-1)=sum_r a_(j,r) U_r.                          (7)

Every convolution coefficient is an integer, and (4) gives

    |c_h|<l*M_block*P<Q/2.

As Q is even, the stronger integer bound |c_h|<=Q/2-1 follows. This strict margin controls the entire low tail, not just each coefficient separately. With T=Q^(l-1), define

    low=sum_(h=0)^(l-2) c_h Q^h,
    high=sum_(h=l)^(2l-2) c_h Q^(h-l).

Then

    |low| <= (Q/2-1)*(T-1)/(Q-1) < T/2,
    |d_j| < Q/2,
    F_j=low+T*(d_j+Q*high).                                (8)

The high quotient is an unrestricted integer and can have either sign. Nothing in the argument assumes a nonnegative product or no carries in the usual nonnegative radix expansion.

For each product supply six positive integers named low_positive, low_slack, dot_positive, dot_slack, high_positive, high_negative. Define, by paid arithmetic,

    low=low_positive-T_half,
    d_j=dot_positive-Qhalf,
    high=high_positive-high_negative.

Impose the three comparisons

    F_j=low+T*(d_j+Q*high),
    low_positive+low_slack=T,
    dot_positive+dot_slack=Q.                              (9)

These give the strict intervals -T/2<low<T/2 and -Q/2<d_j<Q/2. They uniquely recover (8): two such decompositions differ by a multiple of T in their low terms, while that difference has absolute value less than T, so the low terms agree. Dividing the equality by T, the middle terms differ by a multiple of Q and have difference of absolute value less than Q, so the middle terms agree. The high difference is then determined.

Conversely (8) supplies positive offsets low+T/2 and d_j+Q/2 and positive complementary slacks. Represent its signed high by

    high_positive=max(high,0)+1,
    high_negative=max(-high,0)+1.

These max operations are a mathematical witness choice, not operations used in the polynomial source. The common additive freedom in the two high ports changes neither the extracted value nor the ordinary-input projection.

Equations (7) and (9) directly supply the four fixed-group matrix increments. The two context-SWITCH selected outputs and their four fixed multiplications remain unchanged. There are no word-sum coordinates, coefficient offsets, or separate selector-center corrections.

## 4. Full positive-zero theorem

Soundness follows in this order: the integer finalizer forces all outer comparisons; block/global bounds permit the native bootstrap; the joined AND recovers selected words and (4); balanced extraction then proves that every history increment is the exact chosen matrix action. The old first-disagreement bound, chronological controller flow, typed SWITCH pre-state, LOAD growth k<D and marked population equation force k=x. The unchanged fixed-program membership and unary initialization theorem therefore applies to the ordinary input.

For completeness take an accepted atomic path and the parent's sufficiently large dyadic D. Its positive history and block hats, SWITCH hats, terminal fields and global slack remain valid, since the complete packing fields H,M,Z,q are unchanged. The old global bound

    bound_global >= ((K-12)D+5)J >0

still applies. Choose the new extraction witnesses by (8)–(9). All twenty comparisons hold and all supplied coordinates are positive. The inherited native converse supplies fresh positive native witnesses as before. This proves the same full positive-zero input projection; it does not assert an all-value identity of the complete polynomial or a bijection of witness tuples.

More specifically, positive zeros of the frozen 3,162-operation source and of this source have the same projection to all their common non-extraction ports. These include the ordinary input, fixed coefficient ports, native witnesses, history and edge ports, height and global-bound slacks, terminal fields, population quotient, the two block hats and block slacks, and the SWITCH hats. The projection excludes every middle-coefficient and word-sum extraction hat, offset, slack and high-quotient port, even when the two sources reuse its textual name. In particular the dot and low slacks are not required to retain their old values.

Keep the stated non-extraction ports: (2) leaves every native cut identical. After the shared typing theorem, (8)–(9) extend an old zero to the new extraction coordinates. Conversely the old nonnegative products and word sums have the bounded positive extensions proved in the packed-output note. The free common offset in the new high-positive/high-negative pair precludes any claim of a unique inverse.

Zero input, absent LOADs, zero selected blocks, zero products and empty TILE words create no endpoint exception: the balanced offsets are then positive half-scales, and high=0 can use high_positive=high_negative=1. A mandatory SWITCH still guarantees a nonempty physical history. Ordinary positive input is the restriction x>0.

## 5. Complete source cost and degree

| Complete array | Packing | Native | Outer producers | Finalizer | Total | M,A | Positive witnesses |
|---|---:|---:|---:|---:|---:|---|---:|
| Diagnostic |93|63|84|62|302|126M,176A|55|
| Original fixed table |896|63|1,441|62|2,462|1,124M,1,338A|150|

There are twenty comparisons: the inherited six, two block bounds and twelve balanced-product comparisons. Each product has six positive ports. The two word sums and their six ports disappear, while the four signed high quotients add four ports relative to the previous single positive high hats. The net saving is two witnesses. The complete actual array uses 684 distinct integer literals, with largest absolute literal C=2^93 (94 bits). The half-radix, half-low scales, every coefficient multiplication and all bounds/finalization gates are included. All rows and free ports are structurally live; no optimality is claimed.

The native packing fields are identical polynomial functions of their common ports, so the native factor degrees remain

    4727,8506,5684,3780,3780,7560,2,

with sum 34,039. This includes the parent's all-value main-norm cancellation. The diagnostic native sum remains 1,351.

The signed block increases the outer degree. For a block of length l, its selector pack has degree 2l-1; multiplying by c0 gives U_block degree 2l. A reversed coefficient polynomial has degree at most 2l-2, so its product reaches 4l-2. This degree is attained in each actual block: at least one of the two first-lane coefficients is nonzero, and the leading form is a nonzero constant times

    -c0_leading * S_last_leading * Q_leading^(2l-2).

In the longest block l=194, S_last is the LOAD edge word, a nonzero independent polynomial. Its first fixed matrix is G_TILE1=[[-489,271],[-895,496]], so the two highest reversed coefficients are -490 and 271, both nonzero. The product's degree 774 strictly exceeds the right side of its extraction comparison, whose degree is at most 2l+1=389. Other comparisons have lower degree. Hence the SOS has exact degree 1,548, and the complete source degree is **34,039+1,548=35,587**. No native unit equation is used to reduce this polynomial degree.

For the diagnostic, at least one signed coefficient polynomial in a length-two block has degree two and its signed block has degree four. Thus an extraction residual has exact degree six, the SOS degree is twelve, and the complete degree is **1,351+12=1,363**. These leading-form statements hold for every valid fixed-program coefficient specialization because C and K are positive and the independent supplied ports remain independent.

## 6. Source and bounded evidence

The standalone helper is adapted by source copying and new arithmetic from the frozen emitter; no predecessor Python is executed or imported. Its strict dependencies are authenticated as inert source text, proofs or JSON. Both complete arrays, all coefficient lists, split selector packs, extraction ports, fixed constants and ledgers are saved in the receipt. Parsing rejects duplicate JSON keys and receipt equality is recursive and type-exact.

The [fresh source](matrix193_balanced_output_scout.py) and [receipt](matrix193_balanced_output_scout.json) have these frozen SHA-256 values:

| Artifact | SHA-256 |
|---|---|
| Python | `e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a` |
| JSON | `63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf` |

All six predecessor pins were authenticated. The receipt records 32 complete modular source/direct-formula comparisons across the two arrays and two primes. Ten diagnostic outer histories, x=0 through 4 with zero or two IDLEs, were evaluated through every literal nonnative source row; their balanced extractions include negative and zero cases. A dense specialization of the complete diagnostic attains degree 1,363 with coefficient 769,157,052 modulo 1,000,000,007.

A separate bounded component check covers 2,992 signed convolutions at even radices 4,6,8,16 and block lengths two and three. All complete low tails satisfy the strict bound and the balanced extraction is exact; 1,032 cases have negative high quotients and 280 have zero products. These are integer convolution checks, not native histories or an exhaustive source-domain certification.

The actual saved 83-TILE+SWITCH trajectory is also reconstructed, with all four products and signed decompositions computed exactly. Two products and two high quotients are negative. All twenty mathematical outer comparisons, positive supplied outer fields and native input fields, and the joined AND hold. D has 476 bits, B has 561 bits, Q has 47,134 bits and q has 22,247,342 bits. Its H/M/Z/q digest is exactly the frozen packed-output value `69354b5e33fc40c1990a31713d5ae17b53265374f1590b2ae26b6082f983f610`; all ten diagnostic packing digests also match their parent values.

The actual fixture is at x=0 in the saved illustrative context. The enormous literal outer DAG is not reevaluated exactly for that fixture; the complete-source modular comparisons and the independent mathematical formulas have the stated complementary scopes. No native Pell tuple is materialized. Native extension and uniform fixed-program acceptance are mathematical conclusions of the proofs, rather than conclusions drawn from finite fixture counts.

Fresh normal and optimized exact receipt replays from working directory `/` both passed. Once the trio and its pinned dependencies are installed together, replay with:

```sh
replay_wip=/absolute/path/to/native-stream-queue
python3 "$replay_wip/matrix193_balanced_output_scout.py" \
  --root "$replay_wip" --expect "$replay_wip/matrix193_balanced_output_scout.json"
python3 -O "$replay_wip/matrix193_balanced_output_scout.py" \
  --root "$replay_wip" --expect "$replay_wip/matrix193_balanced_output_scout.json"
```
