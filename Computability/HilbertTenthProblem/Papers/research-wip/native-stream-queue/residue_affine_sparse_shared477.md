# One-program U21 compiler with 477 paid operations

The complete [source and receipt](residue_affine_sparse_shared477.json) compute
the same polynomial as the saved
[one-program sparse U21 compiler505](residue_affine_sparse_control_codes.md)
in **477 = 176M + 301A operations**, saving28 operations. The source retains
**67 positive witnesses**, ordinary positive input x, a single fixed program
parameter E, and the inherited degree bound **at most5091**. Its certificate
has **457 = 169M + 288A operations** and seven comparisons in the parent's
convention. Every emitted row is live.

The proof is an exact all-value identity to the actual505 array on identical
supplied coordinates. Therefore the full positive zero sets and the parent's
ordinary-input universality theorem transfer directly. This is an independent
substrate improvement above the separate84-operation universal polynomial;
no circuit minimum or exact-degree claim is made.

## 1. Actual one-program parent

The immediate source is the default shared coupled-product array stored
in `residue_affine_sparse_control_codes.json`, which contains all505 rows.
The new helper reads that array directly. Its two parameters are `program`
and `input`, denoted E and x; only E is fixed per represented program.
The complete U21 recipe supplies E=3^e. The retained height and radix rows
are literally

    height_83 = program + input
    height_85 = height_83 + height_slack
    radix_86 = 64 * height_85.

Thus h=E+x+eta and B=64h. Both height additions and the multiplication by64
remain paid. There is no supplied `radix_program` port and no separate
program-dependent radix multiplier. In particular no C>E assumption from
the two-parameter504 construction enters this proof or its recipe.

The inherited positive domain gives h>=3 and E<h<B. The original table,
prime payloads, injective control codes, positive computed scale, native
AND bootstrap, remainder conditions, chronological transports, paid
x-doubling loader and finalizer remain unchanged as polynomials.
The represented-set theorem is inherited on valid fixed E=3^e recipes;
arbitrary numerical diagnostics are not certified as compiler programs.

The arithmetic strategy is the same as the separate
[two-parameter476 source](residue_affine_sparse_shared476.md), but the saved
source, exact identity, interface, degree bound and receipt here are
independently checked against505. Some utility code was copied as inert
text and adapted. No predecessor helper is imported or executed, including
the476 helper. The new [standalone helper](residue_affine_sparse_shared477.py)
uses only the Python standard library.

## 2. Three exact paid rewrites

Write E_j=edgej_hat−1 and J=sum_j E_j for j=0,...,35. The parent already
pays seven prime-class sums. Their edge sets are

    {2,3,13}, {32,33,34}, {26,27,35}, {16,17,28,30,31},
    {6,7,10,18,19,20,21,24,25}, {5,8,9,14,15}, {4,11,12}.

Together with the already paid loader pair {0,1}, the already paid state
pair {22,23}, and singleton {29}, these partition all36 selectors.
The checker expands every one of these ten terms to its actual edge
variables and verifies disjointness and complete coverage. This is a
formal linear identity, requiring no Boolean or positivity assumption.

Keep the first loader-pair addition of the old J chain. Replace the next
34 additions by nine additions joining these ten paid terms, preserving
the final register `selectors_70`. This saves **25A**. The class/state
producers depend only on selectors and are moved before J without any
new arithmetic. Their complete paid definitions and all36 hat subtractions
remain in the emitted source.

The parent has already paid `repeat_odd_318=1+P+P²`. Its separate
`three_range_repeat_408=1+P(P+1)` and private product
`range_repeat_shift_407` can therefore be removed, using `repeat_odd_318`
in the sole range-mask consumer. Exact expansion in the actual scale P
proves equality, saving **1M+1A**. No new power or repunit is supplied.

Finally let W be the quotient word, U=W+J, V the prime-weighted word,
S the complementary remainder word, and I,D,T the increment, decrement
and positive-test selectors. Here T is the literal edge_14. The actual
parent computes

    Z=J−I−D−T,
    common_payload=U+V−S−Z.

These six additions/subtractions can be replaced by the five operations
computing

    common_payload=W+V−S+(I+D+T).

This uses U−J=W and saves **1A**. Both current/following payloads retain
this exact common value, and U remains paid for its other consumers.
The old private Z chain disappears. The retained intermediate names
`common_quotient_152` and `common_remainder_153` change value; their only
remaining path passes through the restored `common_payload_154`.
They are explicitly excluded from the same-value register claim.

Total saving:25A+(1M+1A)+1A = **1M+27A =28 operations**.

## 3. Full source identity and inherited positive domain

The checker expands the three local identities exactly over integer
polynomial rings and binds them into both full source expression graphs.
It compares all465 other retained registers, including the actual computed
packing/native inputs, all72 native-prefixed rows, all six ordinary
residuals, the full factor product and output. All20 finalizer rows are
literal parent rows. The source therefore satisfies, over every
commutative ring,

    F477(E,x,witnesses)=F505(E,x,witnesses).

Every supplied coordinate is identical on both sides. This proves equality
of the entire positive integer zero sets, not only an implication between
selected histories. No new witness, reconstructed height or signed inverse
is needed. The parent's universal ordinary positive-input representation
and its uniform polynomial degree bound5091 follow from this full identity.
No independent recertification of the historical U21/native compiler chain
or new exact-degree proof is claimed.

The only newly emitted array is the default shared coupled-product source.
Other historical plans, unshared forms and SOS variants are not claimed as
emitted477-operation successors.

## 4. Complete ledger and fresh evidence

| Stage | M | A | Operations |
|---|---:|---:|---:|
| Actual505 parent certificate |170|315|485|
| New certificate |169|288|457|
| Unchanged finalizer |7|13|20|
| Complete new polynomial |**176**|**301**|**477**|

The complete source removes38 old names and introduces ten paid new names.
A fresh dependency traversal counts every row and verifies unique definitions,
sequential operand availability, binary operation types, full liveness and
all69 free ports: E, x and67 positive witnesses. The literal one-program
height/radix rows are checked in both arrays. The certificate count is derived
from the actual emitted rows outside the retained20-row finalizer.

The original505 source hash is authenticated and checked against its saved
source binding. The rewrite uses fresh edited lists and explicitly checks
that the original parent array stays byte-identical in memory before any
parent/child comparisons. The receipt binds to the new helper's exact bytes.
Duplicate JSON keys are rejected, and canonical receipt comparison preserves
number types; explicit guards remain active under optimized Python.

In addition to the exact full-source proof,32 signed modular source pairs
and four signed rational source pairs agree in complete outputs and checked
interfaces. These are off-zero algebra diagnostics, not accepted histories
or full native Pell zeros. The positive-zero theorem rests on the symbolic
identity, not on those finite evaluations.

Fresh normal and optimized exact receipt replays from `/` both pass:

```sh
u21_wip=/absolute/path/to/native-stream-queue
python3 "$u21_wip/residue_affine_sparse_shared477.py" \
  --root "$u21_wip" --expect "$u21_wip/residue_affine_sparse_shared477.json"
python3 -O "$u21_wip/residue_affine_sparse_shared477.py" \
  --root "$u21_wip" --expect "$u21_wip/residue_affine_sparse_shared477.json"
```

All predecessor code was treated as inert text/data. No repository or frozen
predecessor file was modified.

## 5. Frozen provenance

The following six files are authenticated before the saved parent source
is interpreted:

| File | SHA-256 |
|---|---|
| `residue_affine_sparse_control_codes.py` | `433c4d87af47d166d8c26db4e879a77e12a3fbcf3e7a1bf8c125701b2b21a4a7` |
| `residue_affine_sparse_control_codes.json` | `2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d` |
| `residue_affine_sparse_control_codes.md` | `be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da` |
| `residue_affine_sparse_factored.md` | `b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7` |
| `residue_affine_sparse_scale538.md` | `0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623` |
| `residue_affine_sparse_terminal537.md` | `9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1` |

New helper SHA-256:
`21463ce43e33aea904401277940f83990e033018ab624d8367b11c7eee9c2b0f`.
New receipt SHA-256:
`3472269ef557bfbcb6dd2697f9a780990bb394d7e370cadb282f7b03a4cd3716`.
