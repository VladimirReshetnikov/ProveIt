# Factoring the computed native index saves four additions

After computing all four native fields, their only remaining purpose is
to construct the packed native index. Reassociate this private arithmetic
and fold one fixed offset into an existing padding gate. This removes
**four literal additions**, leaving the entire final polynomial identical
over all supplied integer assignments.

The six-field parent is the
[unsquared outer product](group_projective_unsquared_outer_product.md).
The four-field parent is the
[computed-checksum SOS](group_projective_computed_checksum_field.md).
The same local rewrite applies to both. No comparison, witness,
positivity argument, ordinary input or compiler constant changes.

Use the existing notation and fixed-table hypotheses

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

The resulting complete ledgers are

| Native variant and final polynomial | Certificate | Equations | Positive witnesses | Polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|Four-field, full SOS|C-1|12-chi|m+30-chi|C+34-3chi|22nu L+54|
|Six-field, unsquared outer product|C-1|10-chi|m+28-chi|C+28-3chi|nu(27L+m+15)+46|

The illustrative ten-letter six-field example with both optional
projections now has **257 certificate / 283 polynomial operations,
nine equations, 43 positive witnesses and degree 2376**. Without
controller-mask reuse it has **258/284 operations and degree 1944**,
with the same equation and witness counts.

These are complete fixed-table formulas. The universal numerical matrix
alphabet remains uninstantiated, and the separate numerical universal
75/88 frontiers are unchanged.

## 1. The exact polynomial identity

Use mathematical names A,B for the old padded inputs, and Zp for the
already paid padded output:

    A=16H+12, B=16M+10, Zp=F3=16Z+8,
    F1=A-Zp, F2=B-Zp,
    F0=q-F1-F2-Zp-1.

The index is computed by the parent's Horner chain:

    r=F0+qF1+q^2F2+q^3Zp.

Substituting the checksum and factoring q-1 gives

    r=(q-1)[1+F1+(q+1)F2+(q^2+q+1)Zp]
     =(q-1)[A+1+(q+1)(B+(q-1)Zp)].              (1)

Thus, directly in the joined fields,

    r=(q-1)[(16H+13)+(q+1)((16M+10)+(q-1)(16Z+8))].

Equation (1) is an integer polynomial identity; it requires no native
typing, positive field bound, checksum equation imposed at a zero,
or special value of q. The checksum is already a computed definition
in the parent. The source verifies (1) symbolically before checking
the actual complete compiler.

The offset is **13** in the first padded field. The second padded
field remains **16M+10**, and the output remains **16Z+8**.
The source changes the existing padding addition from 12 to 13;
it does not compute a new A+1 using an extra gate.

## 2. The private source fragment and exact saving

In the parent, computing F1,F2,F0 takes five additions: two port
differences and three checksum differences. Its Horner index takes
three multiplications and three additions. This eleven-gate fragment
therefore costs `3M+8A`.

Delete those eleven gates, adjust the existing A padding offset, and
insert the following seven gates:

    qm=q-1, qp=q+1,
    v=qm*Zp,
    u=B+v,
    v2=qp*u,
    S=(16H+13)+v2,
    packed_r=qm*S.                               (2)

The new fragment costs `3M+4A`. It computes the same packed index
by (1), so exactly four additions disappear. In the four-field variant,
the comparison of supplied r with this packed index remains explicit.
In the six-field variant, every native r consumer still uses the same
computed packed-index register.

The [source](group_projective_factored_native_index.py) checks the exact
old gate patterns and every consumer of each deleted register. The old
padded-A register is used only inside that fragment, and no retained
comparison consumes it. It can therefore be changed by one without
affecting another interface. The packed-r register is preserved by name
and value. Every other retained comparison and certificate register
keeps its exact polynomial value.

The source topologically orders the replacement and checks the M/A
counts. Its `rewrite(old_packet)` API permits composition with later
changes, while `build` provides both complete variants. Historical
field metadata does not supply an uncounted arithmetic gate: none of
the deleted private field registers appears in the final source or
its comparisons.

## 3. Why the earlier positive-domain proofs still apply

The new supplied-coordinate list is exactly the parent's list. For
every such assignment, the retained residuals are identical, and the
final polynomial is identical. Thus the integer and positive zero sets
are equal on the same witness vectors.

The earlier proofs may still reconstruct the mathematical fields
F0,F1,F2 from their definitions when establishing positivity and native
typing. These reconstructions are proof steps; the actual certificate
now computes their combined index directly by (2). There is no new
positive existential field or omitted defining equality. Reusing the
parent theorem does not require materializing unused intermediate
registers in every arithmetic implementation of the same polynomial.

The same exact polynomial identity also proves the inherited degrees
in the opening table. This reduction changes the arithmetic circuit,
not the output polynomial. Both the six-field product polynomial and
its earlier SOS alternative save four operations under the rewrite.
The latter retains its old degree `nu(38L+2m+30)+52`.

## 4. Checks and scope

The [receipt](group_projective_factored_native_index.json) stores twenty
compact variant ledgers and one complete ten-letter certificate and
final product source. It checks the symbolic identity (1), the exact
consumer sets, the retained comparison list and witness list, and
every literal operation count.

Across 1,280 complete-source assignments, including 320 signed
assignments, it verifies every surviving register, every residual and
the full final polynomial against the actual parent. The one changed
padding register differs by exactly one as specified. The packed index
and output agree exactly, including off the zero set.

The exact degree is inherited by polynomial equality, rather than
estimated from finite evaluations or recomputed by expanding an
unchanged high-degree output. The parent packets retain their exact
factor-degree audits. Run normally for deterministic receipt comparison
or with `--write` to regenerate it.

Independent proof/source review and a fresh default replay passed with
no findings. Another 256 signed assignments across both native variants
and both compiler switches independently checked the direct field/index
formulas, every retained residual, complete outputs and exact M/A saving.
