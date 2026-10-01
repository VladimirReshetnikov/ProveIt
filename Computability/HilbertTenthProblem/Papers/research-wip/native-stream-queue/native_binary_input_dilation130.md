# Inline the two shifted inputs of the complete binary recoder

The exact positive relation

    z=sum_j bit_j(x)*16^j

now costs **130=67M+63A**, with the same49 positive witnesses and34
comparisons as [the complete132 recoder](native_binary_input_dilation132.md).
Its sum-of-squares polynomial costs **231=101M+130A** and has exact
degree40. The complete polynomial is identical to the parent's
polynomial on every supplied integer assignment, including assignments
away from its zero set.

Only two private shifted-input additions disappear. Both native kernels,
the exponent synchronization, mask construction, congruence and bounds
remain paid. This is not a change to the ordinary-input interpretation or
an unproved positive-coordinate elimination.

## 1. Exact local rewrite

The parent first computes `copies=xJ`, then uses

    Hhat=copies+1, scaled_A=16Hhat, padded_A=scaled_A-4,
    Mhat=K+1, scaled_B=16Mhat, padded_B=scaled_B-6.

The new source uses

    scaled_A=16*copies, padded_A=scaled_A+12,
    scaled_B=16*K, padded_B=scaled_B+10.               (1)

The two padded values are identical by the polynomial identities

    16(copies+1)-4=16*copies+12,
    16(K+1)-6=16*K+10.                               (2)

The source audits the exact parent instructions and their consumers:
Hhat feeds only scaled_A, Mhat only scaled_B, and each scaled product
feeds only its displayed padded value. None of those four private
registers occurs directly in a comparison. Hhat and Mhat can therefore
be deleted; the two private scaled products change value, but every
other retained register, every residual and the full polynomial stay
identical. No downstream comparison is dropped or rewritten.

In particular (1) pays both products by16 and both additions of fixed
numerals. No parent arithmetic is silently reused after being removed,
and no copy operation is charged as a new gate. These are complete
literal replacement instructions.

## 2. Positive domains and complete equivalence

The supplied coordinates and their positive domains are unchanged.
On every positive supplied tuple, the conceptually restored parent
values `Hhat=xJ+1` and `Mhat=K+1` are strictly positive before invoking
either native kernel. They are computed parent registers, not missing
existential witnesses. Their arithmetic has been incorporated exactly
into the paid padding instructions (1).

All34 residuals agree for arbitrary integer tuples by (2) and the
consumer audit. Hence the positive zero sets are the same on the same
49 witnesses. The parent's full theorem applies unchanged: geometry47
at B>=8q^2 links q's binary exponent to the repunit duration; AND64
types the second power and selects the diagonal bits; the paid shifted
quotient and output bound recover the unique folded value. Its full
positive converse, including the x=1 quotient shift and all-ones input
boundary, is retained without another hypothesis.

## 3. Ledger, degree and repeated coding

Each line of (1) has two gates instead of the parent's three. Thus two
additions are saved:

| Source | M | A | Total | Equations | Positive witnesses |
|---|---:|---:|---:|---:|---:|
| Complete132 parent |67|65|132|34|49|
| Inline successor |67|63|130|34|49|
| Inline sum-of-squares polynomial |101|130|231|1|49|

Because the entire polynomial is identical, its exact degree40 and
leading form are unchanged. The source also repeats the exact weighted
residual-degree check against the parent, without relying on equations
that hold only at solutions.

For r>=1 successive complete recodings, with intermediate positive
outputs supplied and shared between stages, the literal ledger becomes
130r operations,34r equations and50r-1 positive witnesses. One polynomial
costs232r-1 and still has exact degree40. The coded bit width is4^r.
The parent's distinction between a paid word-code primitive and a full
PCP program/history certificate remains in force; no new numerical75/88
claim follows from this rewrite.

## 4. Executable audit

The [source](native_binary_input_dilation130.py) and
[receipt](native_binary_input_dilation130.json) verify the two symbolic
padding identities, every private-register consumer, all gate and
domain counts, and1,024 complete graph/residual/polynomial identities,
including384 signed supplied assignments. They also compare384 genuine
outer word constructions against the parent's source. The imported
native coordinates in those finite outer checks are placeholders, not
claimed full Pell zeros; their existence is proved by the parent
positive converse.

Normal execution compares the deterministic receipt. Use
`--write-receipt` to regenerate it. The132 source and receipt remain
unchanged and runnable.

Independent `native_controller` review passed the final proof, actual
source and fresh default replay with no findings. It checked the private
consumer audit, unchanged positive supplied domain, exact residual and
polynomial identities,130/231 ledgers, degree40 and repeated-stage
counts. An additional256 independently generated signed assignments
matched every complete residual and sum-of-squares output with the132
parent. The complete geometry and positive native converse were also
reviewed in the parent packet.
