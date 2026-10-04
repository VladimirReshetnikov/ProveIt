# Six lookup columns suffice for the matrix193 local predicate

Unimodularity removes two complete matrix-entry lookups from the saved irregular-selector source. The new real-safe synchronized predicate costs **1153 = 579M + 574A**, and its countdown extension costs **1179 = 591M + 588A**. Each saves **374 = 187M + 187A** against the corresponding 1527/1553 predecessor, with the same state interface and one signed selector per step. Exact degrees remain 192 and 194.

The [helper](matrix193_unimodular_selector.py) and [receipt](matrix193_unimodular_selector.json) contain both complete source arrays, all six coefficient recipes, the actual 96 matched transitions, every residual, the full countdown wrapper, and the initializer/endpoint. This is a fixed-context local and fixed-duration improvement. It does not supply duration-independent packing, positive-coordinate conversion, or a new universal-operation bound.

## 1. Pinned data and fixed numerals

The immediate parent is [matrix193_irregular_selector.md](matrix193_irregular_selector.md). Its frozen trio is authenticated as inert bytes:

| File | SHA-256 |
|---|---|
| matrix193_irregular_selector.py | 2ffdae00fe9f41e42f7b8230340ab9345a9dfb813317c8a43a2823647d930a38 |
| matrix193_irregular_selector.json | 8811d84fb6d7ad07270e0a0718c6ec866e21bbb7b40de835d8f06abe7b55f05e |
| matrix193_irregular_selector.md | 81d46fcf7c3a8dea5df229b7e1d5e6c485f2e8b8e466677e7ea24b59112d36a5 |

The six parent dependency files, the Newton-selector and lookup-scout trios, are also individually authenticated by their unchanged hashes. The helper checks all three JSON self-source identities and the immediate parent's dependency map. No predecessor Python is imported or executed. Reused parsing, arithmetic and emitter utility text is present inside this standalone helper; its new identities are independently expanded from direct formulas.

The literal table has 96 paired actions `(K_i,G_i)`, in the same cleanup-first order 109,110,111,112 followed by the remaining old order. Both matrices of every pair have integer entries, determinant 1, and nonzero upper-left entry. These **192 determinant and nonzero-entry hypotheses** are checked directly from the saved table. Choosing K and G independently remains forbidden.

The selector labels and scale are unchanged:

\[
 z_i=(G_i[0]-G_0[0])/5,\qquad G_0[0]=2269607724776857561,
 \quad d_i=\prod_{k\ne i}(z_i-z_k),\quad D=\mathop{\rm lcm}_i|d_i|.
\]

The 96 nodes are distinct signed integers, `z_0=0`; their maximum magnitude bit length is 66. Put `P_0=1`, `P_j(z)=product_(k<j)(z-z_k)`, and `Q=P_96`. For each of the six retained columns `K0,K1,K2,G0,G1,G2`, define

\[
 c_{v,j}=\sum_{i=0}^{j}v_i
 \frac{D}{\prod_{0\le k\le j,\ k\ne i}(z_i-z_k)},
 \qquad L_v(z)=\sum_{j=0}^{95}c_{v,j}P_j(z).                \tag{1}
\]

Each quotient is an exact fixed integer: its denominator divides `d_i`, hence divides D up to sign. Equivalently compute the integer scaled divided-difference table from `b_(0,i)=D v_i` and

\[
 b_{j,i}=(b_{j-1,i+1}-b_{j-1,i})/(z_{i+j}-z_i),\qquad c_{v,j}=b_{j,0}.
\]

The same denominator argument holds on every consecutive subset. The fresh helper checks all **27,360** divisions for zero remainder, independently checks (1) at **48** selected coefficients, and verifies all **576** exact interpolation values `L_v(z_i)=D v_i`. All retained fixed-numeral fingerprints agree with the parent.

There are 473 nonzero coefficient bindings plus D, hence **474 live fixed numerals**. The actual receipt gives their effective integer recipes, sign/bit length/SHA-256 metadata, and every variable source use. The scale has **211,075 bits** and the maximum coefficient has **211,154 bits**. These are fixed integer leaves under the inherited arbitrary-numeral cost convention. Their data-compilation divisions are not variable gates; every multiplication by a fixed numeral in the source is paid. No restricted-constant or bit-complexity bound is asserted.

## 2. Why the fourth matrix entry is unnecessary

Let

\[
 M=\begin{pmatrix}a&b\\c&d\end{pmatrix},\qquad ad-bc=1,\quad a\ne0,
\]

act on a row `(u,v)` to produce `(p,q)`. Define its ordinary action errors

\[
 e_0=p-au-cv,\qquad e_1=q-bu-dv.
\]

At its selector node the three retained lookup values are `A=D a`, `B=D b`, `C=D c`. Use the two paid residuals

\[
 r_0=Dp-Au-Cv,\qquad r_1=Aq-Bp-Dv.                       \tag{2}
\]

For unrestricted scalar values there is an exact polynomial identity

\[
 r_0=D e_0,\qquad
 r_1=D(ae_1-be_0)+Dv(ad-bc-1).                          \tag{3}
\]

The helper proves (3) coefficientwise, before any determinant substitution. Under the checked matrix hypothesis the correction vanishes. The transformation from `(e_0,e_1)` to `(r_0,r_1)` has determinant `D^2 a`, which is nonzero. Therefore `(r_0,r_1)=(0,0)` is equivalent to the full row action over arbitrary real numbers, and consequently over integers. Negative a is harmless; no state divisibility or positivity condition is needed. Nonzero a is essential and is never inferred off the selector nodes.

Apply (2) once using K and once using G. The complete synchronized polynomial is

\[
 U=Q(z)^2+r_{K,0}^2+r_{K,1}^2+r_{G,0}^2+r_{G,1}^2.       \tag{4}
\]

It is nonnegative over all real ports. A zero forces `z=z_i` for some actual table label, then (3) forces exactly the matched action `(K_i,G_i)`. Conversely every matched action extends to a zero by taking its node. Thus existentially quantifying the selector gives exactly the same real and integer transition relations as the parent. A label is unique once z is fixed; endpoints alone need not determine a unique tile.

This is **zero-relation equivalence**, not all-value equality of the old and new sums of squares. The ordinary row errors undergo a nonorthogonal transformation, and off-node interpolated matrices need not be unimodular. The square of Q is retained: the unchanged signed integer `-14438573412727439787` has `Q<0`, so the consecutive-node argument for omitting that square is unavailable.

## 3. Complete paid source and degree

The parent prefix of 190 rows is identical. All 934 retained lookup rows agree with the parent after register renaming. The entire K3 lookup removes 92M+92A=184 rows; the G3 lookup removes 95M+95A=190 rows. Their fixed-numeral bindings also disappear. The new four residuals still cost 3M+2A each, so the residual/SOS suffix remains 29 rows.

| Full source stage | M | A | Total |
|---|---:|---:|---:|
| Shared shifts and prefix products | 95 | 95 | 190 |
| Six lookup outputs, 467 nonconstant terms | 467 | 467 | 934 |
| Four residuals, five squares and final sum | 17 | 12 | 29 |
| **Synchronized** | **579** | **574** | **1153** |
| Complete unchanged countdown suffix | 12 | 14 | 26 |
| **Countdown** | **591** | **588** | **1179** |

The first three K columns retain the three initial zero nonconstant coefficients; G0 remains `D*G_0[0]+5D*z`. These give exactly 103 zero nonconstant coefficients across the six columns. Every saved row, supplied port and declared fixed-numeral binding is live. The two complete arrays contain **2,332 rows** in total. No global minimality is claimed.

The helper expands all 97 shared prefix polynomials and checks all 473 lookup coefficients in independent prefix variables. A separate exponent-vector ring verifies all **25 coefficients** of the entire new state/SOS suffix at independent lookup, scale and state ports. Thus the proof covers every consumer and the final sum, not just the interpolation outputs.

The residuals in (2) have total degree at most 96 in independent state and selector ports. Q is monic of degree 96. Setting all state ports to zero and `z=t` makes the full literal source exactly `Q(t)^2`, attaining degree **192** with leading coefficient 1. The full countdown specialization also sets `n=t,next_n=0` and is exactly

\[
 (t-1)^2\bigl(Q(t)^2+t^2\bigr),                         \tag{5}
\]

attaining degree **194** with leading coefficient 1. Both identities are checked on the literal DAG using exact specialization and polynomial arithmetic. Pruning expressions annihilated on these proof lines deletes no paid row from the saved source. Fixed numerals have degree zero.

## 4. Countdown, endpoint and ordinary input

The parent countdown suffix is retained row for row, up to its tile-output wire and register names. Its polynomial is

\[
 U_{\rm count}=E_{\rm load}\bigl(U+n^2+(n')^2\bigr),
\]

where the five-square `E_load` enforces

`X'=X, Y'=Y B^(-1), n'=n-1`,

with `B^(-1)=[[52891,-29036],[94920,-52109]]`. The helper independently expands all **62 wrapper coefficients** and checks both factors. Over the reals a local zero is precisely LOAD, or a matched TILE with `n=n'=0`. A LOAD does not constrain the selector, which can always be chosen as integer 0.

The literal initializer remains `X=(35426321,-19628667), Y=(1,0), n=x`, with **zero input gates**. The complete endpoint source is

\[
 (X_0-Y_0)^2+(X_1-Y_1)^2+n^2,
\]

costing **7=3M+4A**. Its seven coefficients, closure, liveness and degree 2 are independently checked. Both initializer and endpoint are retained in the receipt.

For natural ordinary input x, the inherited signed-counter proof is unchanged: every LOAD decreases n by 1, every TILE requires n zero, and the endpoint requires n zero. Thus exactly x loads occur, all before any tile; an accepting trajectory has shape `LOAD^x TILE*`. All real state trajectories from this integer initializer are integer by induction, because every allowed action has integer coefficients. Arbitrary real selector values during LOAD do not change the states, and every real accepting trajectory has an integer-selector extension. The parent's faithful row encoding and directed-semigroup acceptance theorem remain explicitly inherited dependencies.

For fixed duration h>=1, sum the h nonnegative countdown predicates directly with the endpoint, paying h joins. This gives **1180h+7 operations, 6h signed witnesses, and degree at most 194**. The synchronized supplied-target version gives **1154h+5**, with 5h signed witnesses and degree at most 192. Neither bound asserts exact degree after arbitrary initial substitutions. Duration still controls the arity; unbounded fixed-arity packing and a paid conversion to positive coordinates remain open.

## 5. Bounded evidence and replay

In addition to the unrestricted coefficient identities and full source accounting, the helper checks:

- all 192 actual unimodular matrices have nonzero first entry;
- all 576 column/node interpolation values, 27,360 exact compiler divisions and 48 independent coefficient formulas;
- all 190 unchanged prefix rows, 934 retained lookup rows and 26 unchanged wrapper rows;
- 35 full high-bit evaluations: matched/wrong actions at seven table nodes in both arrays, rational nonnodes, and loader examples including a rational counter;
- 416 full modular evaluations against a separately written nested-Newton and residual reference: every one of the 96 nodes, matched/wrong successors, and 16 further signed tuples per array.

The modular checks are supplementary exact congruences, not a proof of zero existence or a replacement for the polynomial identities. No archived code, historical builder, full long trace or predecessor suite was executed. An independent mathematical challenge of (3), its domain assumptions and the degree argument found no gap.

Fresh normal and optimized exact replays from `/` pass. With the nine pinned dependencies and this trio installed:

```sh
unimodular_wip=/absolute/path/to/native-stream-queue
python3 "$unimodular_wip/matrix193_unimodular_selector.py" --root "$unimodular_wip" --expect "$unimodular_wip/matrix193_unimodular_selector.json"
python3 -O "$unimodular_wip/matrix193_unimodular_selector.py" --root "$unimodular_wip" --expect "$unimodular_wip/matrix193_unimodular_selector.json"
```

Exactly one of `--expect` and `--output` is required. Output creation is exclusive. JSON duplicate keys and noninteger numeric syntax are rejected; receipt comparison preserves exact types, and checks remain active under `-O`. This is a bounded saved-source CLI, not a maintained arbitrary-input compiler API.
