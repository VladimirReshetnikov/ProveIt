# Joint state factors reduce the complete matrix source to1399 operations

The four complete sources now cost **1405 / 1402 / 1402 / 1399 operations**,
saving **ten multiplications** in each source. The coefficient component is
**540 = 292M + 248A**, down from550. All supplied coordinates, full
polynomials and positive zero sets agree with the corresponding frozen
[cleanup-tail parent](matrix193_cleanup_tail_fusion.md).

The saving comes from moving a shared, already paid power of Q through both
columns of each of five state blocks. It is a joint evaluation of multiple
expressions. No division, new witness, additional fixed numeral, conditional
zero equation or selector assumption is used.

## 1. Exact paid factor identities

Use the baseline names. Q is the actual computed `r108`. The following powers
are already paid and remain live:

| Register | Value |
|---|---|
| `r143` | Q^12 |
| `r145` | Q^48 |
| `cp383` | Q^66 |
| `cp117` | Q^78 |
| `r161` | Q^72 |
| `r138` | Q^18 |

In each block below, remove the four indicated multiplication rows and use
their unscaled operands throughout that block. Move the original addition
at each listed terminal output to a fresh paid register, then multiply that
sum by the listed existing factor, retaining the original output name.

| Block | Four removed products, replaced by their unscaled operands | Two terminal restorations |
|---|---|---|
| X12 | `cp113→cp112`, `cp134→cp133`, `cp145→cp144`, `cp148→cp147` | `cp235`, `cp238`, each multiplied by `r143` |
| X48 | `cp166→cp165`, `cp177→cp176`, `cp155→cp154`, `cp182→cp181` | `cp267`, `cp270`, each multiplied by `r145` |
| Y66 | `cp384→cp381`, `cp387→cp386`, `cp390→cp389`, `cp393→cp392` | `cp474`, `cp477`, each multiplied by `cp383` |
| Y12 | `cp396→cp395`, `cp399→cp398`, `cp402→cp401`, `cp405→cp404` | `cp446`, `cp449`, each multiplied by `r143` |
| Y78 | `cp363→cp362`, `cp372→cp371`, `cp354→cp353`, `cp375→cp374` | `cp462`, `cp465`, each multiplied by `cp117` |

There are five accompanying retained-definition edits:

    cp121 = cp383 * cp120;
    cp438 = cp434 * r161;
    cp439 = cp437 * r161;
    cp490 = cp486 * r138;
    cp491 = cp489 * r138.

For X12, the second summand in the old `cp122` also has the common factor:

    old cp113 = Q^12 * cp112,
    old cp121 = Q^78 * cp120 = Q^12 * (Q^66 * cp120).

Thus the changed `cp121` and the removed `cp113` let `cp122`, as well as the
other three indicated entries, be evaluated with their Q^12 factor deferred.
Every downstream operation up to `cp235` and `cp238` is linear in those
entries, with its other operand unchanged. Both terminal values are restored
by their paid products with Q^12. The X48 and Y78 blocks have the same
four-factor/two-restoration structure.

Y66 and Y12 each have four terminal contributions. Two of them already had
a paid multiplication by Q^6. After the common factor is deferred, use the
existing Q^72=Q^66*Q^6 or Q^18=Q^12*Q^6 in that same row. These are the edits
to `cp438,cp439` and `cp490,cp491`. Only the other two contributions need new
restoration products. This use of existing paid powers is the reason the
joint rewrite saves operations.

For example, write the unscaled four Y66 entries as a,b,c,d. Its old first
pair of intermediate sums is

    Q*(Q^66*a)+Q^66*b = Q^66*(Q*a+b),
    Q*(Q^66*c)+Q^66*d = Q^66*(Q*c+d).

The following constant linear combinations still carry Q^66. Their existing
final Q^6 multiplications are replaced by Q^72 multiplications. The other
two linear combinations receive a Q^66 multiplication after their sums.
These are polynomial distributive identities, including at Q=0 and over
rings with zero divisors. The construction never obtains a new value by
dividing an old value by Q.

## 2. Complete source and cost

The [fresh helper](matrix193_joint_state_factor.py) authenticates the full
parent trio and the original controller-map receipt as inert data. It checks
every550-row coefficient mapping from the baseline into each chart, every
removed product and every actual power binding. All five block rewrites are
simultaneous, and the complete graph is rescheduled and checked for cycles,
sequential operand availability and output liveness.

Exactly20 old multiplication identifiers disappear. Exactly10 identifiers
are introduced for the terminal sums: those additions were already paid at
the ten old target names. Each target name now contains its restoration
multiplication. Thus the ten additions remain paid, and twenty old products
are replaced by ten restoration products. The net saving is10M and0A.
All remaining source rows outside the coefficient component are literal.

| Variant | M | A | Complete | Positive witnesses | Exact degree inherited |
|---|---:|---:|---:|---:|---:|
| No controller chart |673|732|**1405**|141|35,587|
| Flow |672|730|**1402**|140|53,345|
| Population |672|730|**1402**|140|53,347|
| Both |671|728|**1399**|139|71,105|

The receipt contains all5608 source rows. The coefficient cone is540 in
each array, and all242 selector rows,97 grouped-population rows and63 native
rows remain literal. The native and finalizer rows are interleaved with
other producers; their boundaries are checked by names and the actual output
expression, not inferred from contiguous slices. The full finalizers remain
50/47/47/44 rows with16/15/15/14 ordinary residuals. Every operation and all
150/149/149/148 supplied ports are live. The eight fixed coefficient ports
and143 distinct integer literals are unchanged.

## 3. Exact values, complete identity and semantics

The helper evaluates every pure-Q cone as an exact integer polynomial,
anchoring Q to its actual complete upstream expression in both arrays. The
other rows are interpreted as exact expression DAGs. This checks the
polynomial identities without replacing a computed field by an unrelated
free parameter.

There are124 surviving internal coefficient registers per chart whose
values change deliberately. Each is checked to satisfy

    old_value = Q^e * new_value,
    e in {12,48,66,78}.

The receipt lists their exact names, exponent and old/new polynomial hashes.
The exponent multiplicities are56/34/20/14 respectively. These are computed
registers, not supplied coordinates. No assertion is made that all old
intermediate values are retained.

All fourteen terminal contributions are restored exactly. Their actual
chart names, old/new definitions and full polynomial coefficient vectors
are recorded. All four complete coefficient words in each chart match the
parent's exact saved vectors: sixteen words and2704 coefficient entries.
The numbers of surviving old registers that do retain their values are
1271/1268/1268/1265. The ten introduced sums have no claimed old counterpart.

Most decisively, the complete output DAGs agree after exact pure-Q
normalization. For each of the four variants j this proves

    F_new,j(x, fixed_context, witnesses)
      = F_parent,j(x, fixed_context, witnesses)

over every commutative ring on identical supplied coordinates. In particular,
the identity holds at Q=0. All complete positive integer zero sets agree by
the identity map. The inherited ordinary-input theorem on the parent's
valid fixed-context recipes transfers unchanged; no new native tuple needs
to be reconstructed for this rewrite.

The earlier terminal-carry and IDLE steps retain their ordinary-input-only
inverse scope. This packet does not strengthen those historical maps. Exact
degrees transfer by full polynomial equality, not by a new independent
leading-form derivation. Fresh syntactic propagation gives the separate
upper bounds36,547/54,785/54,785/73,023. No new universal84 improvement or
circuit-minimality claim is made.

## 4. Provenance and replay scope

| Inert dependency | SHA-256 |
|---|---|
| `matrix193_cleanup_tail_fusion.py` | `52113307be60663b792a5ac62a7dc18ca35355d1a534faba4163c9b6d6047089` |
| `matrix193_cleanup_tail_fusion.json` | `61cbef79077bc3c5527c71f0abbeaac967f3d342f83bb8b9019ccdaa89857fe1` |
| `matrix193_cleanup_tail_fusion.md` | `0791bf4f25ae06e5ea4729de70da27d201524b57596756d991ad1af8253ebcc6` |
| `matrix193_entry_controller_charts.json` | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |

Only the new standard-library helper executes. It reads no predecessor as
Python, preserves the parent packet unchanged, rejects duplicate JSON keys
and noninteger number encodings, binds its own bytes and each complete source
array into the receipt, and uses explicit checks under optimization. Receipt
creation requires a fresh path; exact replay uses type-sensitive canonical
JSON comparison.

The coefficient computations here are exact polynomial certificates for the
entire changed source, not samples of accepting histories. No new numerical
native Pell fixture or history diagnostic is claimed. No repository or frozen
predecessor file was modified.

The writer and fresh normal and optimized exact receipt replays from `/`
passed. Installed replay uses:

```sh
matrix_wip=/absolute/path/to/native-stream-queue
python3 "$matrix_wip/matrix193_joint_state_factor.py" \
  --root "$matrix_wip" --expect "$matrix_wip/matrix193_joint_state_factor.json"
python3 -O "$matrix_wip/matrix193_joint_state_factor.py" \
  --root "$matrix_wip" --expect "$matrix_wip/matrix193_joint_state_factor.json"
```

New helper SHA-256:
`a146ffe90c441c288a71acef624e58ec5b35f8f210747fdcc76fcb7210df6df7`.
New receipt SHA-256:
`dfcd4ae7ab908804b141a0fe4feb93be8b31c3cc776a3ad2fbe78136ce71e154`.
