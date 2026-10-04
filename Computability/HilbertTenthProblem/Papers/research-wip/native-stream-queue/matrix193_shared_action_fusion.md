# Shared matrix action reduces the complete matrix source to 1393 operations

The four complete sources cost **1399 / 1396 / 1396 / 1393 operations**,
saving **4 multiplications and 2 additions** in each source relative to the
[joint-state parent](matrix193_joint_state_factor.md). The coefficient component
is **534 = 288M + 246A**, down from 540. All supplied coordinates and every
retained old register have identical values. The complete polynomials,
positive zero sets, ordinary-input recipes and exact degrees are unchanged.

This is a new fusion of two fixed matrix actions. The parent's ten
multiplications saved by postponing powers of Q are already included in the
starting source and are not counted again.

## 1. The exact two-output identity

Use the parent's baseline register names. In the actual source,

\[
 A=\begin{pmatrix}-489&271\\-895&496\end{pmatrix},\quad
 u=(\mathtt{cp480},\mathtt{cp483}),\quad
 v=(\mathtt{cp415},\mathtt{cp493}),
\]

\[
 p=\mathtt{r138}=Q^{18},\qquad
 q=\mathtt{cp129}=Q^{60},\qquad
 z=(\mathtt{cp502},\mathtt{cp505}).
\]

Here Q is the actual computed register `r108`, with its unchanged complete
upstream expression. The old paired outputs are

\[
 (\mathtt{cp504},\mathtt{cp507})=z+p(uA)+q(vA).
\]

Evaluate instead

\[
 s=pu+qv,\qquad
 (\mathtt{cp504},\mathtt{cp507})=z+sA.
\]

Linearity proves the identity over every commutative ring, including Q=0.
In fact p,q and the six coordinates of u,v,z may be independent values:
no property of the coefficient words, selector masks, matrix determinants,
native witnesses or positive zeros is required. The helper expands this
independent eight-port identity as exact sparse integer polynomials, in
addition to checking the actual complete source bindings.

The four fixed entries of A were already used as literal operands. Both
powers p and q are already paid and remain live. All four products in pu and
qv, both additions forming s, all four fixed-coefficient products in sA, and
both additions forming sA are explicitly paid in the new source. The two
additions of z remain paid at `cp504` and `cp507`.

## 2. Literal source replacement and paid cost

Remove the eighteen private parent rows

```text
cp484 cp485 cp486 cp487 cp488 cp489 cp490 cp491
cp494 cp495 cp496 cp497 cp498 cp499 cp500 cp501
cp503 cp506
```

Their only consumers are within that set or the two retained outputs
`cp504,cp507`. The helper records and checks the full consumer map in each
chart. Replace those two output definitions and introduce exactly these
fully paid rows:

```text
fusion_u0   = r138 * cp480
fusion_v0   = cp129 * cp415
fusion_s0   = fusion_u0 + fusion_v0
fusion_u1   = r138 * cp483
fusion_v1   = cp129 * cp493
fusion_s1   = fusion_u1 + fusion_v1
fusion_a0   = -489 * fusion_s0
fusion_b0   = -895 * fusion_s1
fusion_out0 = fusion_a0 + fusion_b0
fusion_a1   = 271 * fusion_s0
fusion_b1   = 496 * fusion_s1
fusion_out1 = fusion_a1 + fusion_b1
cp504       = cp502 + fusion_out0
cp507       = cp505 + fusion_out1
```

The eighteen deleted rows cost 12M+6A. The twelve new rows cost 8M+4A.
The two changed output rows are additions before and after the rewrite.
Thus the net saving is exactly **4M+2A**. The complete graph is rebuilt,
checked for cycles and sequential operand availability, and checked for
liveness of every row and every supplied port; the count is not an estimate
from an isolated subexpression.

For the three controller charts, every parent register reference above is
translated by the authenticated original controller map. New `fusion_*`
register names are fresh in each separate array. The fixed matrix and the
operation pattern do not vary across charts.

| Variant | M | A | Complete | Positive witnesses | Exact inherited degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |669|730|**1399**|141|35,587|
| Flow |668|728|**1396**|140|53,345|
| Population |668|728|**1396**|140|53,347|
| Both |667|726|**1393**|139|71,105|

The receipt saves all **5584 source rows**. Each coefficient component has
534 rows; all rows outside that component remain literal, as do all retained
coefficient definitions except the two output additions. In particular the
parent's 242 selector rows, 97 grouped-population rows and 63 native rows
are unchanged. The helper explicitly traces the complete finalizers:
50/47/47/44 rows and 16/15/15/14 ordinary residuals, including interleaved
producers. These finalizer rows and residual definitions are literal.

There are still 150/149/149/148 supplied ports, eight fixed coefficient
ports and 143 distinct integer literals. No witness, constant recipe,
selector group or native input is added or removed.

## 3. Complete identity, positive domains and degree

The helper interprets the old and new arrays together. It binds Q to its
actual upstream expression, then normalizes every pure-Q computed value
as a dense polynomial in Z[Q]. Other operations are interpreted in a shared
expression DAG. It verifies that **all 1387/1384/1384/1381 retained old
registers** agree, including the two rewritten outputs. No surviving
internal-state change or division is needed in this packet.

All four saved complete coefficient words in every chart are re-expanded
and matched exactly: **sixteen words and 2704 coefficient entries**. The
paid values Q^18 and Q^60 are also checked explicitly. The native product,
every final residual and the full output agree under the same computed-Q
binding. Thus, for each chart j,

\[
 F_{\mathrm{fusion},j}(x,\text{fixed coefficients},\text{witnesses})
 =F_{\mathrm{joint},j}(x,\text{fixed coefficients},\text{witnesses})
\]

as integer polynomials on identical supplied coordinates.

The positive integer zero sets therefore agree by the identity map. The
parent's ordinary-input theorem transfers on exactly its valid fixed-program
coefficient recipes. No new native extension or accepting-history fixture
is necessary for this algebraic rewrite. This identity does not strengthen
the ordinary-input-only inverses of earlier terminal-carry or IDLE steps.

The uniform exact degrees in the table transfer by equality of the full
polynomial on the same variables, with the same fixed-numeral conventions.
They are not claimed from a new dense expansion of the complete high-degree
polynomial. Separate syntactic propagation still gives the upper bounds
36,547/54,785/54,785/73,023. This alternate matrix route remains above 84;
there is no new claim about the original complete84 source or global
arithmetic minimality.

## 4. Provenance and replay

The [fresh helper](matrix193_shared_action_fusion.py) authenticates these
frozen dependencies and reads them only as bytes or inert JSON:

| Dependency | SHA-256 |
|---|---|
| `matrix193_joint_state_factor.py` | `a146ffe90c441c288a71acef624e58ec5b35f8f210747fdcc76fcb7210df6df7` |
| `matrix193_joint_state_factor.json` | `dfcd4ae7ab908804b141a0fe4feb93be8b31c3cc776a3ad2fbe78136ce71e154` |
| `matrix193_joint_state_factor.md` | `d0032f9c9ba8975983c7fabf5399e6b1b590751598a61e53879d0a80f95fffce` |
| `matrix193_entry_controller_charts.json` | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |

The helper rejects duplicate JSON keys and noninteger number encodings,
preserves the parent object unchanged, binds its own bytes and all four
complete source arrays to the receipt, and uses explicit checks that remain
active under `python -O`. Receipt creation uses an exclusive output path;
replay compares type-sensitive canonical JSON.

The writer and fresh normal/optimized exact replays from `/` passed. No
frozen helper was executed or imported. Only the new helper executes;
there is no new numerical history or native Pell fixture, and no repository
file was edited by this author.

```sh
matrix_wip=/absolute/path/to/native-stream-queue
python3 /tmp/matrix193_shared_action_fusion.py --root "$matrix_wip" \
  --expect /tmp/matrix193_shared_action_fusion.json
python3 -O /tmp/matrix193_shared_action_fusion.py --root "$matrix_wip" \
  --expect /tmp/matrix193_shared_action_fusion.json
```

Helper SHA-256:
`e54e4d04c394ed5c889c6ff48d59c6dd2bfd1cd6af56513d0be949bf16725ed8`.
Receipt SHA-256:
`6dcdd1dfe0b4dbc71c9263c45dc5773d39672673db3ef3742c6ecc63222eb1ca`.
