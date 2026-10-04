# Irregular integer labels reduce the complete matrix193 local source

The actual96 matched matrix actions admit a complete **1527=766M+761A** real-safe local predicate. Its ordinary-input countdown extension costs **1553=778M+775A**. Each saves **188 operations** against the consecutive-label real-safe predecessor, with the same one additional signed selector per step. Exact degrees remain192 and194.

The construction pays for both complete source arrays, all coefficient uses, the squared selector polynomial, all four state residuals, and the full26-gate countdown suffix. Fixed coefficients are much larger: the common scale has211075 bits and the largest lookup coefficient has211154 bits. Their exact finite recipes and value fingerprints replace repeated giant literals in the receipt. This uses the parent's arbitrary fixed-integer numeral convention, not a literal1/3 or bit-operation model.

This is a fixed-context local and fixed-duration result. It does not supply arbitrary-duration fixed-arity packing or positive-coordinate conversion, and it does not improve the universal84-operation bound.

## 1. Pinned table, new labels and inherited interface

The [helper](matrix193_irregular_selector.py) reads the frozen [Newton-selector packet](matrix193_newton_selector.md) and [lookup scout](matrix193_lookup_schedule_scout.md) as inert bytes. No predecessor Python is imported or executed. The six authenticated files are:

| File | SHA256 |
|---|---|
| matrix193_newton_selector.py | a8437280c24b844f7cd0c5193ba9421a5be6e93901027023440709d7c74c3eb0 |
| matrix193_newton_selector.json | 21c47a877d2b36a435c3ffd7dbdb46a21a6c96f11c91d60637743ef20f3fbeff |
| matrix193_newton_selector.md | b5cd29a950c1e380969bb3a7cfe924b78a360e7ab2f61fff82151dc627de581e |
| matrix193_lookup_schedule_scout.py | 5913b37641696e216cfb05fb9bd39a27ed72d2480be526df5bba628c6a7c19ce |
| matrix193_lookup_schedule_scout.json | c8205b9b193936f5685d3cb77a068ad5eb5e4b92136c78eb40187198b56e3da2 |
| matrix193_lookup_schedule_scout.md | cc96b4a27da6d846fb257e7d603a662f27d5423266234e2a92f98b6a06d571f3 |

The JSON self-source pins are also checked. The full table is retained: each tile i acts on two signed row vectors by `X'=X K_i`, `Y'=Y G_i`. It is not permissible to choose K and G independently. The cleanup-first order is exactly109,110,111,112, followed by the other rows in their previous relative order; the checker matches it to the scout's saved order.

Index this ordered table by0<=i<96 and let `g_i=G_i[0]`. All96 values are distinct and the gcd of `g_i-g_0` is5. Assign the integer selector node

\[
 z_i=(g_i-g_0)/5,\qquad g_0=2269607724776857561.
\]

These are fixed labels, of maximum magnitude bit length66, with `z_0=0`. The varying selector z is a new existential port. No runtime conversion from a supplied matrix entry, division by5, or externally chosen branch is hidden in this relabeling. Distinctness is an authenticated fact about this saved table; it is not asserted for every possible program-specific table.

## 2. Exact compact fixed-numeral recipe

For each i define the nonzero fixed integer

\[
 d_i=\prod_{k\ne i}(z_i-z_k),\qquad
 D=\operatorname{lcm}_{0\le i<96}|d_i|>0.
\]

For one of the eight integer matrix columns v and0<=j<=95 define

\[
 c_{v,j}=\sum_{i=0}^{j}v_i
     \frac{D}{\prod_{0\le k\le j,\ k\ne i}(z_i-z_k)}.       \tag{1}
\]

Every quotient in(1) is an integer: its denominator divides d_i, and d_i divides D up to sign. The empty product is1. Thus(1) is an effective construction of fixed integer coefficients from the finite saved table, with no number-theoretic existence oracle.

Equation(1) is D times the j-th divided difference at the initial j+1 nodes. The equivalent compiler recurrence is

\[
 b_{0,i}=Dv_i,\qquad
 b_{j,i}=\frac{b_{j-1,i+1}-b_{j-1,i}}{z_{i+j}-z_i},\qquad
 c_{v,j}=b_{j,0}.                                    \tag{2}
\]

The same subset-denominator argument applies to every consecutive subset, so every value in(2) is integral. The fresh helper verifies all36480 remainder-zero divisions. It separately checks(1) for64 coefficients, including the highest order, across all eight columns. These are fixed-data computations performed before interpreting the variable source.

The receipt gives all96 nodes, the actual transition table, formulas(1)–(2), every nonzero coefficient's binding ID, and its sign, magnitude bit length and exact integer SHA256. The integer encoding is the ASCII sign followed by unsigned big-endian magnitude; it is unambiguous. The formula, not its hash alone, specifies the integer. The scale and662 nonzero coefficients give663 fixed-numeral bindings. Zero coefficients have null bindings and emit no source term. All663 bindings are used.

Source operands such as `C:D` and `C:K0:4` denote these computed fixed numerals. They are not variables, additional witnesses, opaque mathematical oracles, or gates with free division. The evaluated source contains only binary addition, subtraction and multiplication. Multiplication by any such numeral is charged. This is the same fixed-numeral leaf convention as the predecessor; constructing the constants from a restricted alphabet would be a different, unpaid cost model.

D has211075 bits. The largest scaled coefficient has211154 bits. The complete receipt, including both full instruction arrays and the coefficient metadata, occupies477773 bytes. It does not repeat hundreds of211k-bit coefficients as literals. This is a representation and coefficient-height tradeoff, not a claim of fast numerical evaluation or small constants.

## 3. Lookup identities and the real transition relation

Define the ordinary polynomials

\[
 P_0=1,\quad P_j(z)=\prod_{k=0}^{j-1}(z-z_k),\qquad
 L_v(z)=\sum_{j=0}^{95}c_{v,j}P_j(z),\qquad Q=P_{96}.
\]

Newton interpolation gives `L_v(z_i)=D v_i` for all96 nodes. The source's95 shifts and95 prefix products are shared by all eight columns. The checker verifies every one of the97 prefix polynomials coefficientwise, and verifies the literal lookup rows as linear combinations of independent prefix symbols: all662 nonzero basis coefficients match the recipe. It also evaluates all768 column/node values exactly. Each lookup has degree at most95.

The selected column is exactly

\[
 L_{G0}(z)=Dg_0+5Dz.
\]

Consequently its coefficients of orders2,...,95 vanish. The first four K matrices are equal, so all four K columns have zero divided differences of orders1,2,3, regardless of the unequal node spacing. The checker verifies that these106 are precisely the zero nonconstant coefficients; all654 other nonconstant coefficients are nonzero and different from±1.

Write `L_K,L_G` for the two row-major arrays of scaled lookup entries. The complete synchronized source is

\[
 P_{\rm sync}=Q(z)^2+
   \|DX'-X L_K(z)\|^2+\|DY'-Y L_G(z)\|^2,             \tag{3}
\]

where each norm is the sum of exactly two scalar squares. A separate exponent-vector calculation checks all25 coefficients of the entire residual/finalizer suffix at independent lookup and scale ports. Thus the interpolation outputs connect to every actual state port and the single final output.

For arbitrary real supplied states, every summand in(3) is nonnegative. A zero forces Q=0, hence z=z_i for exactly one label. Since D>0, the four remaining equations then give the original matched action `(K_i,G_i)`. Conversely every original tile action extends to a zero by choosing its node. Thus existentially quantifying z preserves the parent's real and integer transition relations. Different tiles may agree on special state tuples; uniqueness is per chosen label, not uniqueness from endpoints alone.

This is a zero-relation transfer through a selector relabeling, not equality with the previous off-zero polynomial. The new integer coefficients and scale change off-zero values.

The square of Q is retained. The helper finds the signed integer `-14438573412727439787` where Q is negative. Hence the predecessor's argument for replacing Q² by Q on all integers does not transfer. No claim that the unsquared source is integer-sound is made here.

## 4. Exact arithmetic and degree

The fixed data are leaves; all nonconstant uses appear in the saved rows:

| Synchronized stage | M | A | Total |
|---|---:|---:|---:|
| Shared95 shifts and95 prefix products |95|95|190|
| Eight lookup outputs:654 nonconstant terms |654|654|1308|
| Four state residuals, their squares, Q² and final sum |17|12|29|
| **Complete synchronized** |**766**|**761**|**1527**|
| Retained complete countdown suffix |12|14|26|
| **Complete countdown** |**778**|**775**|**1553**|

The parent real-safe sources cost1715 and1741. The additional94 zero coefficients save94M+94A=188 in each complete predicate. Compared with the parent's integer-only1714/1740 variants, the saving is187; the new predicates also retain the stated real-domain equivalence. The already-used cleanup prefix's twelve omissions are not counted twice. Every row, supplied port and declared fixed-numeral binding is live. No global minimum over node choices or schedules is asserted.

Q is monic of degree96. The four state residuals have degree at most96 in independent state and selector ports, so(3) has degree at most192. Set all state ports to zero and z=t. Then the entire literal source equals `Q(t)^2`, with leading coefficient1, proving exact degree192 without zero-only assumptions.

For the countdown line also set n=t and n'=0. The exact whole source becomes

\[
 (t-1)^2\bigl(Q(t)^2+t^2\bigr),                      \tag{4}
\]

which has degree194 and leading coefficient1. The helper checks these identities by exact zero propagation and polynomial evaluation of the literal DAG. Expressions annihilated on this line are pruned only for evaluating the specialization; they remain paid in the full source. The propagated whole-source degree bounds agree with the attained degrees. Fixed numerals have degree zero, regardless of bit length.

## 5. Countdown, ordinary input and duration

The full26-row suffix is taken from the pinned real-safe parent, with only its synchronized-output wire and register names changed. It is exactly

\[
 P_{\rm count}=E_{\rm load}\bigl(P_{\rm sync}+n^2+(n')^2\bigr),
\]

with the original five-square loader error for

`X'=X, Y'=Y B^(-1), n'=n-1`,

where `B^(-1)=[[52891,-29036],[94920,-52109]]`. An independent62-coefficient expansion verifies the full suffix and both displayed factors. A local real zero is either this LOAD action, or one matched TILE with n=n'=0. The selector is unrestricted in a LOAD branch; it can always be chosen to be integer0.

The initializer remains the zero-gate copy `X=(35426321,-19628667), Y=(1,0), n=x`, and the endpoint remains `X=Y,n=0` with its paid7-gate polynomial. The parent signed-counter proof still applies: a finite path from x to zero contains exactly x loads; any tile requires all these loads to have occurred, and a subsequent load would prevent the zero endpoint. Hence every accepting path has shape `LOAD^x TILE*`. The relabeling does not change the actual integer affine actions, so real state trajectories from integral initial data are integral by induction. Real loader selectors may be nonintegral without affecting the states or existence of integer-selector extensions.

For fixed h>=1, copying the complete countdown source at each step, adding all h nonnegative local outputs and the endpoint, gives

**1554h+7 gates,6h signed witnesses, degree at most194**.

The analogous supplied-target synchronized bound is1528d+5 with5d signed witnesses and degree at most192. These bounds include one selector per step and the joins. They do not assert exact degree after arbitrary initial substitutions. The witnesses still grow with duration. The inherited row-injectivity and directed-semigroup semantics remain dependencies; this packet does not re-prove them or build a duration-independent encoding.

## 6. Bounded evidence and replay

The receipt saves both complete arrays, all3080 live rows, the entire coefficient recipe, selector-to-tile map, inherited initializer/endpoint, exact cuts, ledgers and degree certificates. Besides the unrestricted algebra, the helper performs35 full high-bit source checks: matched and deliberately incorrect steps at seven actual nodes in both predicates, two rational nonnodes in both predicates, and three loader cases, including a rational counter. Every one of the96 nodes is covered by the separate exact768-value interpolation check; the complete expensive DAG is not evaluated at every node. No long historical trace or giant predecessor stream was rerun.

Fresh normal and optimized exact replays from `/` pass. With the six pinned parents and this trio installed:

```sh
irregular_wip=/absolute/path/to/native-stream-queue
python3 "$irregular_wip/matrix193_irregular_selector.py" --root "$irregular_wip" --expect "$irregular_wip/matrix193_irregular_selector.json"
python3 -O "$irregular_wip/matrix193_irregular_selector.py" --root "$irregular_wip" --expect "$irregular_wip/matrix193_irregular_selector.json"
```

`--output` writes a new receipt to a nonexistent file. Exactly one of `--output` and `--expect` is required. The helper rejects duplicate keys and noninteger JSON numerals, uses explicit checks under `-O`, and compares expected receipts recursively with exact types. The maintained scope is a bounded CLI and the saved literal source, not a general public compiler API.
