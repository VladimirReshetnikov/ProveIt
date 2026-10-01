# A paid ordinary-input boundary for a fixed generalized PCP program

The binary recoder can supply both the digits and the length of a padded
input word. This closes the ordinary-input boundary for a fixed
generalized Post correspondence program: all tiles remain fixed while
the ordinary integer x varies. For a four-bit alphabet code the complete
scalar boundary relation costs **136=70M+66A**, with **50 positive
witnesses and 36 equations**. Its sum-of-squares polynomial costs
**243=106M+137A**, with exact degree **40**.

This is a complete Diophantine relation for the input and terminal
boundaries. It is not a complete uniform certificate for the intervening
tile word. A fixed program with a larger alphabet uses the explicit
width-dependent ledger below. The universal 75/88 frontier is unchanged.

The rewriting-to-word-equation strategy is classical; see
[Nicolas, Section 3, Theorem 1](https://arxiv.org/pdf/0802.0726).
The construction here uses a fresh delimiter symbol before binary
coding, keeps the rewriting program fixed, and supplies a paid integer
input convention. Its reflexive case is included explicitly. No small
variable-instance PCP undecidability bound is used as a fixed-program
universality theorem.

## 1. Arbitrary fixed block width, with every power paid

Fix k>=4 and write R=2^k. Define

    spread_k(x)=sum_j bit_j(x) R^j.

The [complete inline recoder](native_binary_input_dilation130.md)
generalizes by computing

    Q=q^k, B=2^(k-1) Q, S=qP

instead of Q=q^4 and B=8Q. All its remaining source instructions and
34 comparisons are unchanged. Multiplication by the fixed numeral
2^(k-1) is paid. The source constructs q^k using binary powering, with

    mu(k)=floor(log2 k)+popcount(k)-1

multiplications. This is a literal fixed addition chain, not free
exponentiation or a minimal-chain claim.

For positive q, B>=8q^2, so the complete shared-B geometry theorem and
its positive witness transport apply. Thus q=2^n. The prescribed AND
kernel types qP as dyadic. Consequently P is dyadic, and

    (B-1)J+1=P, q=2^popcount(J), J>B

force P=B^n, J=1+B+...+B^(n-1), and n>=2, exactly as in the recoder
proof. Here log2 B=kn+k-1. The other repunit comparison gives

    K=1+(2B)+...+(2B)^(n-1), S=(2B)^n.

The paid input bound gives 0<x<q. Since log2 B>n, the copies in xJ
do not overlap. The diagonal mask selects

    A=(xJ) AND K=sum_(j<n) bit_j(x) 2^(k(n+1)j).

Modulo Q-1, this is spread_k(x), which lies in

    1 <= spread_k(x) <= (Q-1)/(R-1) < Q-1.

The unchanged shifted quotient and positive output bound therefore
force z=spread_k(x). Conversely, for any x>0 and any n>=2 with x<2^n,
all outer values above and the original two complete native converses
give every positive witness. In particular the quotient is shifted
because x=1 has A=z; high zero padding never changes z.

The result is a complete relation with 49 positive witnesses, 34
equations, **128+mu(k)** certificate gates, split **65+mu(k) M and
63 A**. Its SOS costs **229+mu(k)**, split **99+mu(k) M and 130 A**.
At k=4 this is precisely the established 130/231 count.

## 2. The certified padded length pays for arbitrary fixed framing

For a word over digits 0,...,R-1, let

    val_R(a_1...a_l)=sum_i a_i R^(l-i),
    enc_R(w)=R^|w|+val_R(w).

The sentinel makes this code injective even for words containing digit
zero or the empty word. Fix nonempty prefix p and suffix s. Let b_n(x)
be the n-bit binary expansion of x, padded with leading zeros to length
n and viewed as a word of R-ary digits zero and one. At a recoder zero,

    enc_R(p b_n(x) s)
      =R^|s| [enc_R(p) Q+z]+val_R(s).               (1)

Both z and Q come from the same proved exponent n. The four instructions

    C=enc_R(p)*Q, D=C+z,
    E=R^|s|*D, Vinitial=E+val_R(s)                  (2)

therefore pay for the entire framed input. They cost 2M+2A, including
the two fixed-numeral products. No separate logarithm, leading-bit test
or input-length oracle is assumed. Q is not an arbitrary supplied
padding length after the native comparisons hold.

The padded convention is deliberate. Any semidecider on ordinary positive
integers can first ignore leading binary zeros, then process the
remaining input. That is a fixed finite machine, and its acceptance is
independent of n whenever n>=2 and x<2^n. This requires no arithmetic
normalizer beyond the full input relation already paid above.

## 3. A fixed rewriting program for the padded input

Fix a deterministic Turing machine with finite tape alphabet Gamma
containing 0,1 and blank, finite states, an initial state q0, and a
distinguished accepting state qa. State symbols, tape symbols and fresh
markers L,R,# are disjoint. Represent a finite configuration by

    L a_1...a_j q b_1...b_l R, l>=1,

with the scanned symbol immediately after q and all omitted tape cells
blank. The initial word is

    u_n(x)=L q0 b_n(x) R.

Compile a transition (q,a)->(p,b,right) into

    q a c -> b p c          for each tape symbol c,
    q a R -> b p blank R.

For a left move use

    c q a -> p c b          for each tape symbol c,
    L q a -> L p blank b.

A stationary move is q a -> p b. At the accepting state add cleanup
rules qa a -> qa and a qa -> qa for each tape symbol a. The fixed
target is v=L qa R. The accepting state has no ordinary transitions.

Every rule has nonempty left and right sides and contains no #. Before
qa is reached, a valid configuration has exactly the transition rewrite
specified by the machine, including its boundary blank extension. Every
result remains a valid configuration. Cleanup cannot begin before qa,
and afterward it can erase all tape symbols on both sides to reach v.
Thus u_n(x) derives v iff the fixed machine accepts the padded input.
No erasing rule introduces a new accepting state. This proves the
fixed rewriting program's soundness as well as completeness.

For any recursively enumerable set of positive integers, choose its
fixed padded-input semidecider above. This gives an effective fixed
rewriting program for that set. No numerical small-state universal
machine or minimal alphabet bound is asserted here.

## 4. Fixed tiles and a single varying boundary

Include a copy tile (a,a) for every configuration-alphabet symbol and
for #. Include a tile (l,r) for every fixed rewrite rule l->r. Let
sigma,tau be the two morphisms on tile sequences. All these tiles are
independent of x and n. Then

    u_n(x) derives v
      iff exists a finite tile word w:
          sigma(w) # v = u_n(x) # tau(w).           (3)

Here the tile word may be empty in the general definition, though (3)
with these nonempty boundaries has no empty solution.

For the forward direction, factor each rewrite step into unchanged
prefix copies, one rule tile and unchanged suffix copies. Separate
these tile words with the copy tile for #. The two sides in (3)
telescope through all intermediate configurations. For a zero-step
derivation u=v, use the copy word for u; this also satisfies (3).

For the reverse direction put X=sigma(w), Y=tau(w). Each rule tile
gives one allowed rewrite in its surrounding context, so X derives Y.
The fresh delimiter cannot be crossed, created or removed by any rule.
Write X=X_0#...#X_r and Y=Y_0#...#Y_r. Equality (3) gives

    X_0=u_n(x), Y_0=X_1, ..., Y_(r-1)=X_r, Y_r=v.

The derivation restricts to X_i deriving Y_i in each delimiter region.
Concatenating these derivations proves u_n(x) derives v. Thus (3) is an
exact fixed-program generalized PCP interface, not an inference from
undecidability of variable tile tables.

Choose k>=4 large enough to assign distinct k-bit blocks to every
configuration symbol and #, assigning digits zero and one to the input
symbols 0 and 1. Extend the assignment by concatenation. Fixed-length
injectivity preserves (3) in both directions. No comma-free property is
needed: rewriting is proved over the symbol alphabet before applying
the injective coding to the complete word equation.

## 5. Exact affine matrix and scalar boundary interface

Regard each fixed k-bit block as one radix-R digit. Lengths in this
section count these blocks, not their individual binary bits. A tile
(a_i,b_i) acts on positive sentinel accumulators by

    M_i=[ R^|a_i|     0        val_R(a_i) ]
        [    0     R^|b_i|    val_R(b_i) ]
        [    0        0             1   ].

Start from (1,Vinitial,1), with p=L q0 and s=R # in (1). A common
selected tile word produces

    Ufinal=enc_R(sigma(w)),
    Vfinal=enc_R(u_n(x) # tau(w)).

Equation (3) is now exactly the terminal comparison

    R^|#v|*Ufinal+val_R(#v)=Vfinal.                 (4)

Its product and addition cost 1M+1A. The supplied Vinitial, Ufinal and
Vfinal are ordinary positive parameters of this boundary component;
the initial first accumulator is the fixed numeral one. The recoder
output z becomes one more positive existential coordinate. All matrix
slopes, offsets, prefix and suffix numerals depend only on the fixed
program. The two copies of its tile sequence are still the same word.

The [source](gpcp_fixed_program_input_bridge.py) compares the computed
input value in (2) with supplied Vinitial, and compares (4) with Vfinal.
Together with the 34 recoder comparisons, this is a complete positive
36-equation relation with 50 witnesses:

| Component | M | A | Total |
|---|---:|---:|---:|
| Complete recoder |65+mu(k)|63|128+mu(k)|
| Input framing |2|2|4|
| Terminal comparison expressions |1|1|2|
| Complete scalar boundary |68+mu(k)|66|134+mu(k)|
| Boundary SOS polynomial |104+mu(k)|137|241+mu(k)|

The exact polynomial degree is **2 max(20,k+1)**. The unchanged
prescribed-AND norm has a nonzero degree-20 highest form. All other
kernel residuals have degree at most 20. The new Q-dependent wrapper
residuals have degree at most k+1; in particular (B-1)J+1-P has the
nonzero leading term 2^(k-1) q^k J when k+1 dominates. The loader has
degree k and the terminal expression degree one. Squared highest forms
cannot cancel in their sum. This proves exact degree in all independent
supplied coordinates, without zero-set simplifications.

For k=4 the boundary is 136/243 with degree 40. This width suffices for
the ten-symbol example in the receipt. For a general universal machine,
choose k from its actual fixed alphabet and use the displayed formula;
do not transfer the numerical example's count to an uninstantiated
alphabet.

The unbounded selected product M_w is not included in this ledger.
Its common choice sequence, weighted histories, typing and geometry
still need a complete Diophantine representation. These matrices have
varying positive slopes and generally nonunit determinants; the existing
SL2 group compiler cannot simply be imported as their history verifier.
The [earlier PCP trace](matrix_pcp_trace.md) identifies those remaining
selected-history obligations. This packet closes its ordinary-input
boundary and fixed-program convention, not the entire arithmetic path.

## 6. Executable evidence and scope

The [receipt](gpcp_fixed_program_input_bridge.json) stores literal source
and finalizer, plus ledgers for widths 4,5,8,16,24. It checks 480 full
residual/SOS evaluations, including 160 signed assignments, and exact
weighted degree computations. Another 320 genuine outer constructions
check variable-width masking, folding, framing and padding invariance.

The source compiles a fixed machine accepting exactly the odd positive
integers into 24 rewrite rules and 34 tiles. Across 189 padded input
runs, it verifies acceptance against parity, materializes the actual
rewrite derivation and common tile word, and compares direct string
images with dense matrix products and every paid boundary expression.
It checks the zero-step case separately and covers left boundary,
interior left and stationary transitions in additional fixtures.
The sample machine is a validation fixture, not a universal machine.

Native coordinates in the genuine outer fixtures are placeholders; the
complete native converses in Section 1 supply their positive extensions.
The finite tests do not claim full numerical Pell zeros or certify all
unbounded selected histories. Normal execution checks the saved receipt;
`--write` regenerates it.

Independent full proof/source/default review passed without findings.
It added 384 signed complete residual/SOS cases at widths 4,7,19,20,25,32,
enumerated 55,987 small tile words and reconstructed all four exact
boundary matches as rewrite chains, and checked 256 machine steps
against an independent tape implementation, including both boundaries.
