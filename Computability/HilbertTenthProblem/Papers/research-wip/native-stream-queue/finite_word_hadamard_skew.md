# Skew packing of a finite binary Hadamard product

For each **externally fixed n>=2**, two length-n binary words have a carry-free product packing whose central n-bit band is their bitwise product. Radix two suffices. A complete emitted graph, including Boolean typing and all four input/packed-word loaders, costs **14n operations**, with **2n+4 positive existential witnesses** and **2n+5 equations**. Its complete sum-of-squares polynomial costs **18n+14 operations** and has degree four. The receipt also emits a variant that constructs every derived numeral from literal two, with the additional cost below.

This is a finite family, not a fixed-arity graph for arbitrary n and not a universal-polynomial bound. The short extraction interface still needs the variable-length loaders and synchronized powers. No claim of optimality, new general AND primitive or improvement over existing native AND constructions is made.

## 1. Prior coverage and precise new scope

The following frozen notes were read inertly; exact byte and read-span hashes are in the receipt. No predecessor helper was executed or imported.

- `native_controller_quadratic_sidon.md`, full: fixed periodic within-cell spacing cannot separate cross-cell products; even rotation preserves the exhibited collision. A growing, paid reversal/spacing interface was left open.
- `input_bridge_central_product.md`, full: one reflected dot-product digit can be extracted conditionally, but the small native radix permits carries and actual false witnesses. That lemma uses a radix larger than the word length and explicit sentinel guards.
- `native_binary_input_dilation129.md` lines1–220 and `gpcp_fixed_program_input_bridge.md` lines1–90: complete positive recoders exist for a **fixed** bit-spacing width. Their larger-width source pays a fixed multiplication chain for q^k and already uses a native AND kernel.
- `matrix193_packed_output_scout.md` lines1–175 and `matrix193_balanced_output_scout.md` lines30–90: fully paid convolution extraction is used across a fixed number of spatial lanes. Their exponents and coefficient-word lengths are fixed table constants, not an unbounded duration.

The present skew exponent layout separates **every input-position pair**, not just a single reflected sum. Its spacing grows with n, so it does not refute the fixed-periodic collision. The complete fixed-n arrays make the loading cost visible. This bounded search of existing WIP is not an exhaustive literature novelty claim.

## 2. Exact central-band identity at radix two

Let `a_i,b_i` be in `{0,1}` for `0<=i<n`, and put

    x=sum_i a_i 2^i, y=sum_i b_i 2^i,
    A=sum_i a_i 2^(n*i),
    C=sum_j b_j 2^((n−1)*(n−1−j)),
    L=(n−1)^2, P=2^L, Q=2^n.

The exponent of the product term `a_i b_j` is

    e(i,j)=n*i+(n−1)*(n−1−j)
          =L+i+(n−1)*(i−j).                         (1)

All n² pair exponents are distinct. If `e(i,j)=e(i',j')`, then
`n*(i−i')=(n−1)*(j−j')`. Coprimality makes n divide `j−j'`; its absolute value is below n, hence j=j' and then i=i'. Every product coefficient is therefore zero or one. There are no binary carries anywhere, including from the whole lower tail.

For i=j, (1) gives e=L+i. For i<j it gives `e−L<=i−(n−1)<=−1`; for i>j it gives `e−L>=i+n−1>=n`. Thus exactly the diagonal terms occupy `[L,L+n)`, and

    floor(A*C/P) mod Q = sum_i a_i b_i 2^i = x AND y. (2)

The proof also works in any integer radix B>=2 with binary coefficients and with P=B^L,Q=B^n. The binary specialization makes the output an ordinary bitwise AND. No hypothesis B>n is necessary. For coefficient digits bounded by d, the same injectivity gives carry-freedom when B>d², independently of n; that extension is only an algebraic observation, not an additional emitted source.

At n=2, A=a0+4a1 and C=2b0+b1. Their product is

    a0*b1 + 2*a0*b0 + 4*a1*b1 + 8*a1*b0.

The bits at positions1 and2 are the desired output. Zero words, zero low remainder and zero high quotient are all allowed. The case n=1 is outside the emitted family; it can be handled by a direct single-bit multiplication, but no such separate source is claimed here.

## 3. A complete fixed-n positive-witness graph

The ordinary integer parameters are x,y and a strictly positive output port Hhat. The represented relation is

    0<=x,y<2^n and Hhat=1+(x AND y).                 (3)

Thus x or y may equal zero; no positive-input compiler convention is being silently changed. The existential coordinates are 2n positive bit hats `ahat_i,bhat_i` and four positive coordinates `low_hat,high_hat,low_slack,output_slack`.

For every bit hat t, compute

    bit=t−1; other=t−2; boolean=bit*other,

and require boolean=0. This charges three operations per bit and, since t is a positive integer, gives t in `{1,2}` and bit in `{0,1}`.

Use four explicit Horner chains:

- x from `a_(n−1),...,a_0` at radix2;
- y from `b_(n−1),...,b_0` at radix2;
- A from `a_(n−1),...,a_0` at radixQ;
- C from `b_0,...,b_(n−1)` at radix`2^(n−1)`.

Each chain starts at its first bit and uses exactly n−1 multiplications and n−1 additions. The first two outputs must equal x,y. The reversal is the literal order of the paid C chain, not a free operation on the supplied y.

For extraction, compute exactly these eight rows:

    product=A*C;
    q_high_hat=Q*high_hat;
    middle_plus_high=Hhat+q_high_hat;
    shifted_upper=P*middle_plus_high;
    rhs=low_hat+shifted_upper;
    lhs=product+(P*Q+P+1);
    low_bound=low_hat+low_slack;
    output_bound=Hhat+output_slack.

Require

    lhs=rhs, low_bound=P+1, output_bound=Q+1.         (4)

Writing `low=low_hat−1`, `high=high_hat−1`, `h=Hhat−1`, equations(4) are precisely

    A*C=low+P*(h+Q*high),
    0<=low<P, 0<=h<Q, high>=0.                      (5)

The offset PQ+P+1 compensates all three positive hats. Euclidean uniqueness makes h the middle band in(2). Conversely the actual low remainder, middle band and upper quotient give positive hats and strictly positive slacks `P−low,Q−h`. In particular when A*C=0, all three hats equal1 and the slacks are P,Q; no sentinel or nonzero product is needed.

Strict positivity of the output port is necessary. If Hhat=0 were admitted, take x=y=Q−1 and their canonical packed product. Its middle remainder is Q−1 and canonical Hhat=Q. Replacing Hhat by0, increasing high_hat by1 and setting output_slack=Q+1 preserves every displayed equation and positivity of the other witnesses. It falsely represents h=−1. Thus the stated Hhat>0 domain is part of the graph, not an optional convention.

The graph therefore has exactly the positive projection(3). All raw inputs and output are determined by the bit guards/loaders and extraction; no uncharged digit oracle is used. Every computed row and every supplied port reaches a comparison or final output.

| Component | M | A | Operations |
|---|---:|---:|---:|
| Boolean guards for2n bits |2n|4n|6n|
| Four Horner loaders |4n−4|4n−4|8n−8|
| Positive extraction |3|5|8|
| Complete certificate |6n−1|8n+1|14n|

There are2n Boolean-zero residuals and five comparison residuals. The Boolean residuals are already computed; explicitly forming the other five costs5A. Squaring all2n+5 residuals costs2n+5M, and joining them costs2n+4A. The complete polynomial thus costs

    (8n+4)M+(10n+10)A=18n+14.

It is a sum of squares, so it vanishes exactly when all equations hold over the integers. Every residual has degree at most two. Each Boolean residual has nonzero quadratic highest part; its square supplies a quartic part which cannot cancel in a real sum of squares. The full polynomial therefore has exact degree four. The degree treats n and all its derived numerals as fixed, not supplied variables.

## 4. Fixed numerals versus fully paid power construction

The14n version permits ordinary fixed integer literals, as explicitly listed in the saved source:2, Q=2^n, `2^(n−1)`, P=`2^((n−1)^2)`, PQ+P+1, P+1 and Q+1. Their values are part of the chosen n-specific source. All multiplication by those literals at runtime is charged. This is not a free variable-exponent POWER call: n is not a parameter of that array, and changing n changes the array and number of witnesses. Literal bit lengths grow quadratically in n.

For readers wanting every derived numeral built from literal2, a second full array is emitted. Let

    mu(k)=floor(log2(k))+popcount(k)−1, k>=1.

The left-to-right binary chain computes2^k in mu(k) multiplications, starting at literal2; mu(1)=0. Separate explicit chains compute Q, `2^(n−1)` and P. They are followed by

    PQ=P*Q; offset_base=PQ+P; offset=offset_base+1;
    Pplus1=P+1; Qplus1=Q+1.

The paid prefix therefore adds

    [mu(n)+mu(n−1)+mu((n−1)^2)+1]M +4A.             (6)

Every subsequent occurrence uses those computed registers. The helper checks that the entire second source contains no integer operands besides1 and2. Chains are deliberately not claimed optimal or maximally shared. At n=2 the reverse radix and P are already literal2; the Q chain costs1M, then PQ costs1M and the four additions are charged, so the extra cost is6, with no missing exponent-zero convention.

All ten complete arrays are saved:

| n | Literal certificate | Literal full SOS | Constructed-constant certificate | Constructed-constant full SOS | Positive witnesses |
|---:|---:|---:|---:|---:|---:|
|2|28|50|34|56|8|
|3|42|68|52|78|10|
|4|56|86|69|99|12|
|5|70|104|84|118|14|
|8|112|158|131|177|20|

These are full arrays with topology/liveness and direct count checks, not totals obtained by assuming a component subtraction. Both variants implement the same relation(3); the second simply pays to construct the fixed numerals.

## 5. The conditional11-operation interface and the remaining loader

If A,C are already correctly loaded and P,Q already correct, the same central-band extraction can be expressed with variable positive integer P,Q by eleven paid rows:

    Pplus1=P+1; Qplus1=Q+1;
    high=high_hat−1; Qhigh=Q*high;
    middle_plus_high=Hhat+Qhigh;
    upper=P*middle_plus_high;
    rhs=low_hat+upper;
    product=A*C; lhs=product+Pplus1;
    low_bound=low_hat+low_slack;
    output_bound=Hhat+output_slack.

The same three comparisons to rhs,Pplus1,Qplus1 enforce(5). This costs **3M+8A**; it has four positive existential extraction coordinates beside supplied Hhat. The offset is now P+1 because the high hat is explicitly decremented. Conditional hypotheses are P>=1,Q>=2 and A,C nonnegative. This graph alone says only that Hhat−1 is the native middle remainder of A*C; it does not say it is the AND of other integers x,y.

For arbitrary n supplied as an integer, the obligations still are

    Q=2^n, P=2^((n−1)^2),
    A=sum_(i<n) bit_i(x)2^(n*i),
    C=sum_(j<n) bit_j(y)2^((n−1)*(n−1−j)),
    0<=x,y<2^n,

with the **same n** everywhere. Merely naming the first two relations POWER leaves them unpaid. Their exponents alone require n−1 and its square if built arithmetically, and a graph for exponentiation still has to be supplied. The last two relations include variable bit-spacing and a length-specific reversal. The existing fixed-k recoder's source and addition chain depend on k; setting k=n at runtime is not authorized by its theorem, and its AND-based method does not independently eliminate the desired AND cost.

The receipt gives small positive extraction aliases when these obligations are omitted:

| Missing obligation | Claimed x,y | A,C | P,Q | Extracted h | True x AND y |
|---|---|---|---|---:|---:|
| Binding loaded bits to x,y |0,0|1,2|2,4|1|0|
| Correct P power |1,1|1,2|1,4|2|1|
| Correct Q power |3,3|5,3|2,2|1|3|
| Reversal |1,2|1,2|2,4|1|0|

All correspond to the intended n=2, and all have positive hats/slacks for the conditional extraction graph. They are not counterexamples to the complete fixed-n source, which retains the missing conditions. They show why the11-operation count cannot be advertised as a complete unrestricted AND relation.

The concrete remaining target is a fixed-arity positive-integer graph for the two synchronized variable-spacing loaders, with all power, reversal, width and digit conditions paid. This note neither supplies that graph nor proves that no inexpensive graph exists. Its exact carry-free layout may be used by a future loader construction; it gives no universal operation bound on its own.

## 6. Fresh evidence and replay scope

The standalone standard-library helper reads only the six frozen Markdown dependencies as inert bytes. Its fresh arithmetic constructs all ten arrays, checks every dependency and live row/port, exact ledgers, Boolean/extraction source structure and quartic upper bound. The all-n proofs above establish the universal statements; the finite checks corroborate them:

- 21,840 complete word pairs for n=2 through7, including all zero-word cases;
- 2,720 full emitted source zeros for both numeral conventions and n=2 through5;
- 2,720 wrong-output perturbations rejected on those full sources;
- 707,263 pair-position checks for n=2 through128;
- the explicit positive missing-loader/power/reversal examples above.

No native Pell tuple, archived suite or predecessor program was run. The predecessor SHA-256/read-span records are in the receipt. Fresh normal and optimized replay use `--expect`; `--output` is exclusive. JSON duplicates are rejected and receipt equality is type-exact. Finite evidence is not a claim of an unrestricted loader, an optimal circuit or a new undecidability theorem.

Fresh author normal and `python3 -O` exact replays from `/` both passed on the final source and receipt. Frozen helper SHA-256: `8bf60fa972867bf690ce116310a59ec91dad458f98a5ed835d18d846402fad2d`; receipt SHA-256: `f4b35fc9c2cc9dd563158f9e44726b90bde94f857f3f900bee3ff684b9a3e4e4`.
