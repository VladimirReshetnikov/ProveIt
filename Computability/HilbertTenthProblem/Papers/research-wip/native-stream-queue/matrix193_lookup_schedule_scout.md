# A bounded lookup-schedule scout for the 96 matrix193 transitions

The four cleanup tiles **109, 110, 111, 112**, placed first in that order, save **24 paid gates** in a shared Newton lookup of the eight transition coefficients. The complete emitted lookup cone falls from **1710 = 855M + 855A** to **1686 = 843M + 843A**. This is a coefficient-lookup component, not an unbounded matrix-product certificate or a universal Diophantine operation bound.

The companion is a standalone standard-library checker. It reads the pinned transition table as inert JSON, imports no predecessor code, and emits both complete lookup arrays. It does not emit the row-update residuals, the final sum of squares, or the countdown wrapper. Those common consumers must be paid by a complete predicate compiler.

## 1. Exact source and domain

The input is the 96-row `transition_table` in [matrix193_synchronized_rows.json](matrix193_synchronized_rows.json), in its literal order. Its eight integer columns are the row-major entries `K0,K1,K2,K3,G0,G1,G2,G3`. The source theorem uses `K` and `G` for the synchronized updates of two signed first rows. This scout inherits that interpretation; it does not re-prove the 193-generator word reduction.

The helper authenticates this entire parent trio:

| File | SHA256 |
|---|---|
| matrix193_synchronized_rows.py | da55246efc8047b6b3f188579cf6c71bbabb067def3fe04ac47ba61b56517e52 |
| matrix193_synchronized_rows.json | 9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233 |
| matrix193_synchronized_rows.md | ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2 |

It checks the JSON self-source hash, table types and distinct tile IDs, and all 288 determinant-one identities. The parent helper is authenticated but never executed. This packet's source SHA256 is `5913b37641696e216cfb05fb9bd39a27ed72d2480be526df5bba628c6a7c19ce`; its receipt SHA256 is `c8205b9b193936f5685d3cb77a068ad5eb5e4b92136c78eb40187198b56e3da2`.

## 2. The paid lookup and selector relabeling

For a chosen ordering, let `v_j` be a column's value at the integer node `j`, let `D=95!`, and put

\[
 P_0=1,\quad P_1=z,\quad P_j=\prod_{k=0}^{j-1}(z-k),\qquad
 I_v(z)=\sum_{j=0}^{95}c_jP_j(z),\quad
 c_j=\frac{D}{j!}\,\Delta^jv_0.
\]

All coefficients are integers. Newton interpolation gives `I_v(j)=D*v_j` at every node. The checker independently evaluates the emitted arithmetic DAG at all 96 nodes for each of the eight columns and both orders: **1536 exact column values**, in addition to the 192 selector zeros. These identities, together with degree at most 95, characterize the interpolants exactly.

The shared producers are the 95 subtractions `z-k` for `1<=k<=95` and the 95 multiplications producing `P_2,...,P_96`. Each nonzero nonconstant coefficient contributes one multiplication and one addition to its column output. Every constant term is nonzero and every nonzero coefficient that is multiplied is different from `+1` and `-1`; the checker verifies these scheduling premises. All 3396 rows in the two saved cones are in the ancestry of `P_96` or a column output.

The literal ordering has all 760 nonconstant coefficients nonzero. For the cleanup order, precisely

\[
 (\text{column},j)\in\{0,1,2,3\}\times\{1,2,3\}
\]

vanish: the first four `K` matrices are identical, hence their first three differences vanish. No other coefficient vanishes. The saved order begins `109,110,111,112,1,2,18,19,21,22,...`; all remaining rows preserve their literal relative order.

A full selector predicate must enforce `P_96(z)=0`, then use the eight column outputs divided conceptually by the fixed scale through **paid equations** such as `D*next_X0 = X0*I_K0(z)+X1*I_K2(z)`. There is no variable division. Under this selector equation, each of the 96 tiles has exactly one selector value in either ordering. Relabeling a selector by its tile ID therefore preserves every transition and gives a bijection between the extended zero sets. The two lookup polynomials are generally different at the same off-node value of `z`; no same-coordinate polynomial identity between the two orderings is claimed. Different tiles can have the same action at special states, so this is uniqueness per chosen tile, not uniqueness from a transition's endpoints alone.

`D` has 492 bits. The largest coefficient magnitude requires 585 bits in the literal order and 574 bits in the cleanup order. Reordering therefore saves the 24 gates without increasing this measured coefficient height.

## 3. Precisely bounded alternatives checked

The augmented table `[1,K0,...,G3]` has rational rank nine. The receipt includes the exact minor on tile IDs `1,2,18,19,21,22,23,24,25`, with determinant

`-2601276742044696425000000`.

Thus no nonzero fixed rational affine relation eliminates one of the eight columns on this table. This statement does not exclude nonlinear relationships or cheaper arithmetic schedules.

There are 72 distinct `K` matrices, with multiplicities `56*1,9*2,6*3,1*4`. For **every repeated-K group**, the scout tries every permutation of that group as a prefix, followed by the other rows in literal order. This is exactly

\[
 9\cdot2!+6\cdot3!+1\cdot4!=78
\]

orders. Twelve is the largest number of zero nonconstant Newton coefficients in this finite family. Every permutation of the four cleanup rows attains it. This is not an exhaustive search over all 96! orders.

A separate ten-order comparison covers literal, reversed, and ascending sorts on each of the eight columns. These ten have no zero nonconstant coefficients and no equal or opposite nonzero coefficients within a common Newton layer. This does not rule out sharing across more complicated combinations of layers.

For the declared nested Newton-Horner schedule, the shared selector-prefix producers remain paid. Literal Horner also costs 1710 gates. Cleanup Horner skips twelve zero additions but still pays the corresponding multiplications, costing 1698. Factoring out the already-paid `P_4` in each of the four `K` interpolants restores the same 1686 count as the shared-prefix schedule. No global circuit lower bound is claimed.

## 4. Distinct irregular nodes: a smaller arithmetic component with much larger numerals

Each `G` column has 96 distinct values. A further exact construction, left as coefficient data and a schedule derivation rather than an emitted full array, uses the literal order and nodes

\[
 z_i=(G_{i,0}-G_{0,0})/5.
\]

The gcd of these differences is exactly 5, so the nodes are distinct integers, begin at zero, and have maximum magnitude bit length 66. Define the positive fixed integer

\[
 D_* = \operatorname{lcm}_{i}\left|\prod_{j\ne i}(z_i-z_j)\right|.
\]

A divided difference on any initial segment is a sum of values divided by the products of differences to the other nodes in that segment. Each such product divides its corresponding full 96-node product. Consequently `D_*` clears every Newton coefficient denominator. The checker performs exact integer divided-difference recurrence and verifies all 768 resulting interpolated values.

The selected column becomes $D_*G_{0,0}+5D_*z$. Exactly its coefficients of orders 2 through 95 vanish; all other nonconstant coefficients are nonzero. The analogous shared-prefix lookup schedule costs **1522 = 761M + 761A**, including all 95 node shifts and 95 prefix products. This count is construction-derived; this packet does not save that large lookup DAG or a complete predicate using it.

Here `D_*` has **211075 bits**, and the largest scaled coefficient has **211159 bits**. A fully repeated hexadecimal coefficient-only JSON representation in the exact format measured by the helper would occupy **35,215,438 bytes**, versus this scout's **794,505-byte receipt**, which includes its two conventional full lookup arrays. The large representation is hashed and measured in memory, not written to the final packet. Compact named fixed numerals or exact integer compiler recipes could avoid repeating those coefficients; this size is a representation measurement, not an arithmetic obstruction.

The irregular selector product is **not** nonnegative on all signed integers. The receipt supplies the integer `-13984527235285535826`, where it is negative. A sum-of-squares construction must retain its square or otherwise prove a suitable nonnegative selector test. The consecutive-node product, by contrast, is zero on `0,...,95` and positive at every other integer, since all 96 factors have the same sign there. That separate domain-dependent simplification is not included in these lookup-only ledgers.

Combining irregular nodes with a cleanup prefix is a further compatible direction, not an emitted or tested full predicate in this packet. No coefficient-height threshold or gate-count optimality is asserted.

## 5. Reproduction and boundaries

From any working directory, with the research-WIP directory and these installed files:

```sh
lookup_wip=/absolute/path/to/native-stream-queue
python3 "$lookup_wip/matrix193_lookup_schedule_scout.py" --root "$lookup_wip" --expect "$lookup_wip/matrix193_lookup_schedule_scout.json"
python3 -O "$lookup_wip/matrix193_lookup_schedule_scout.py" --root "$lookup_wip" --expect "$lookup_wip/matrix193_lookup_schedule_scout.json"
```

Use `--output` instead of `--expect` to write a fresh receipt. The CLI requires exactly one of them. Duplicate JSON keys and nonfinite constants are rejected; expected-receipt equality is recursive and type-exact. The supported surface is this bounded CLI, not a maintained public compiler API.

Fresh normal and optimized replays from `/` pass. No predecessor or archived Python is executed. The finite conclusions concern this pinned 96-row table and the stated schedules. An unbounded product still requires a duration-independent history representation; no such representation or new universal numerical bound is provided here.
