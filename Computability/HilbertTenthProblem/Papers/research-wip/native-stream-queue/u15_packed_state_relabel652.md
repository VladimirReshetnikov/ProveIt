# U15 state relabeling gives the same positive zeros in 652 operations

Swapping the numerical codes of states B and J in the complete
[packed two-tape compiler](u15_packed_two_tape_history.md) saves one actual
multiplication. The ordinary-input polynomial costs **652 = 254M + 398A**,
and the raw-half-tape polynomial costs **409 = 146M + 263A**. Both preserve
the parent's complete supplied-witness zero set on its declared domains.
The parent sources and receipts remain unchanged.

| Interface | Certificate | Equations | Positive witnesses | Complete polynomial |
|---|---:|---:|---:|---:|
| Raw natural half tapes |368 = 132M + 236A|14|54|409 = 146M + 263A|
| Ordinary positive integer input |506 = 205M + 301A|49|105|652 = 254M + 398A|

The four fixed positive program numerals and the ordinary input interface
are unchanged. The inherited formal degree upper bound remains 1936, with
fixed program parameters treated as constants. No exact degree, optimality,
or improvement of the separate 87-operation universal bound is claimed.

## 1. Actual source transfer

The new [compiler](u15_packed_state_relabel652.py) checks the baseline Python
file against SHA256

    ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318

before importing it. It copies the actual `raw_build` and `_build` function
ASTs from those pinned bytes. The numeric rule rows are transformed by

    rho = (0,9,2,3,4,5,6,7,8,1,10,11,12,13,14),

in the original A,…,O order: A retains code 0, B receives 9, J receives 1,
and every other state keeps its old code. Every original rule
`(q,s,r,d,w)` becomes `(rho(q),s,rho(r),d,w)` in exactly the same rule-index
position. All 29 rule selectors keep their meanings and supplied names.
The source AST must contain exactly one `d.mul(9,P)` terminal-state call;
that operand becomes 1. Ordinary multiplication by 1 is eliminated by the
parent DAG builder's existing exact simplification.

The complete raw and ordinary sources are then rebuilt, including the
unchanged paid loader, native AND, comparisons and SOS finalizer. They are
not a hand-picked controller gadget or the old ledger with one subtracted.
The emitted packet retains the primary textual `table` as provenance and
adds `state_relabel` to specify the numeric interpretation; `rules` contains
the transformed numeric table actually used by the source. The complete
sources and all ledgers appear in the [receipt](u15_packed_state_relabel652.json).

The grouped Q and N projections have the same arithmetic counts under this
swap. The only net saving is removal of the terminal multiplication by 9.
There is no new coordinate and no deleted comparison.

## 2. Complete same-witness positive-zero proof

Write `E_i=edge_i-1`. The common source equations and positive domains are
unchanged, so the parent's native AND and range proof recovers the same
dyadic cell geometry

    P=B^t,  B>=64,

and the same chronological one-hot word of original rule indices. This
typing argument uses the retained bounds and native comparisons; it does
not need either numerical version of the state-transport equation. All
head, direction, write and tape projections are unchanged.

For that typed rule word let `(q_j,s_j,r_j,d_j,w_j)` be its original table
rows. The old state equation is

    B * sum_j r_j B^j = sum_j q_j B^j + 9 B^t.

Its coefficients recover `q_0=0`, `r_(j-1)=q_j` at each interior position,
and `r_(t-1)=9`. Every local difference has absolute value at most 14,
strictly less than B, so the usual successive reduction modulo B has no
carry ambiguity. The new equation has rho(q),rho(r) in the projections and
terminal coefficient 1. The same bound applies because rho permutes 0,…,14.
It therefore recovers

    rho(q_0)=0,
    rho(r_(j-1))=rho(q_j),
    rho(r_(t-1))=1.

Since rho is injective, fixes 0, and sends 9 to 1, these are precisely the
same conditions on the original rule word. Conversely every old chronological
word satisfies the new state equation. The unchanged head transport makes
the final read bit 1. The word uses only the 29 defined rules, so the same
first-halt interpretation follows in both directions.

All supplied coordinates, including the complete native witnesses, remain
the same. Thus the identity map is a bijection between the two full zero
sets on the parent's domain: raw L0,R0 are natural and all raw auxiliaries
are positive; the ordinary interface has positive input, fixed positive
program numerals and positive auxiliaries. The paid ordinary loader is
literally unchanged, so the same result holds on each proved universal
program slice. Arbitrary malformed positive program tuples acquire no new
program interpretation.

This proof is not an assertion of equal zero sets on unrestricted signed
native coordinates. Signed inputs are supported for polynomial auditing,
where the exact off-zero identity below is the relevant statement.

## 3. Exact correction on every integer assignment

Keep the original rule-index order. The actual changed affine forms are

    Q_new-Q_old = 8(E2+E3-E18),
    N_new-N_old = 8(E0+E23-E17).

The checker derives these identities as exact sparse affine coefficient
maps from the emitted source, in both raw and ordinary forms. No finite
truth-table inference is used to establish these formulas.

Define

    R = B*N_old-Q_old-9P,
    Delta = 8[B(E0+E23-E17) - (E2+E3-E18) + P].

Then `R_new=R+Delta`. An exact symbolic expression-DAG comparison checks
that every other comparison has the same two polynomials: 13 raw rows and
48 ordinary rows. The comparison order and complete SOS finalizer are
retained. Consequently the entire outputs satisfy, over arbitrary integers,

    F_new-F_old = 2*R*Delta + Delta^2.

The two polynomials are not identical away from their zeros. Same-positive-
zero-set equivalence comes from the typed chronology proof in Section 2.

## 4. API, reproducibility and evidence

The public APIs are:

    build(ordinary=False, *, root=None)
    checked(packet, *, root=None)
    evaluate(packet, values, *, signed=False, root=None)
    polynomial_source(packet, *, root=None)
    verify(root=None)

`root` defaults to the compiler's own directory, so the default sibling
layout works after placing the trio beside its parent. An explicit root
works from any current directory. The CLI is read-only by default:

    python u15_packed_state_relabel652.py
    python /path/to/u15_packed_state_relabel652.py --root /path/to/native-stream-queue

Only `--write` refreshes the adjacent receipt. Assertions must remain enabled.
No `/tmp` import path is built into the compiler.

The parent hash is checked before imports and before public packet access.
Importing the parent temporarily removes all sibling Python module names
from `sys.modules`, including preloaded stubs lacking `__file__` and modules
from another root, then restores the caller's exact previous entries. This
prevents a cached foreign loader from supplying different arithmetic despite
a correct parent-file hash. The parent's native descriptor guards remain
active too.

Public flags require exact Booleans. Canonical packet comparison retains the
parent's recursive exact-type validation; floating coefficients equal to
integers are rejected. Input evaluation calls the parent's original assignment
validator, preserving the complete coordinate set, exact integer requirement,
raw natural parameter boundary, positive witnesses, positive ordinary interface,
and explicit signed-audit flag. Public packets and polynomial sources are
defensive copies of privately cached canonical data.

The writer checks both full compilers, all 29 relabeled rules, all 841 pairs
of rules for adjacency equivalence, 61 exact unchanged comparison identities,
four exact changed affine forms, and 64 complete old/new output corrections
including 32 signed cases. It checks 16 genuine outer histories and their
exact joined bitwise AND. Those fixtures use positive placeholders for native
Pell coordinates; no astronomical complete Pell witness is claimed to have
been materialized. The mathematical native extension is inherited unchanged.

The public-boundary audit includes 948 malformed coefficient, packet, flag
and scalar cases, four defensive-copy checks, and two cold-cache poisoned-loader
regressions (a stub with no file and a module from a foreign root). The first
independent review found the preloaded-module isolation gap; the repaired source
includes those regressions and retains exactly the same emitted arithmetic.

Author writer and fresh default replay passed on repaired source
`cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879`.
An independent complete source, proof and API review passed: 61 exact unchanged
residual DAGs, 96 complete corrections (48 signed), 3,024 individual residual
comparisons, 397 malformed-object rejections, four defensive-copy checks and
two cold fake/foreign-loader isolation checks. Its fresh author receipt replay
also passed. The import-isolation finding is repaired; no finding remains.

This packet follows a bounded 20-permutation scout; that search found no
smaller actual-source count, but it proves no optimality result and is not
run by this maintained compiler.

The [independent review](review_u15_relabel652.md), [checker](review_u15_relabel652.py)
and [receipt](review_u15_relabel652.json) record the complete audit and repaired
import-isolation regression.
